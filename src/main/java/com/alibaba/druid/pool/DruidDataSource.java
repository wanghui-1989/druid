/*
 * Copyright 1999-2018 Alibaba Group Holding Ltd.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package com.alibaba.druid.pool;

import static com.alibaba.druid.util.Utils.getBoolean;

import java.io.Closeable;
import java.security.AccessController;
import java.security.PrivilegedAction;
import java.sql.Connection;
import java.sql.SQLException;
import java.sql.Statement;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.ConcurrentModificationException;
import java.util.Date;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Properties;
import java.util.ServiceLoader;
import java.util.StringTokenizer;
import java.util.TimeZone;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.Future;
import java.util.concurrent.ScheduledFuture;
import java.util.concurrent.ScheduledThreadPoolExecutor;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicLongFieldUpdater;
import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReentrantLock;

import javax.management.JMException;
import javax.management.MBeanRegistration;
import javax.management.MBeanServer;
import javax.management.ObjectName;
import javax.naming.NamingException;
import javax.naming.Reference;
import javax.naming.Referenceable;
import javax.naming.StringRefAddr;
import javax.sql.ConnectionEvent;
import javax.sql.ConnectionEventListener;
import javax.sql.ConnectionPoolDataSource;
import javax.sql.PooledConnection;

import com.alibaba.druid.Constants;
import com.alibaba.druid.TransactionTimeoutException;
import com.alibaba.druid.VERSION;
import com.alibaba.druid.filter.AutoLoad;
import com.alibaba.druid.filter.Filter;
import com.alibaba.druid.filter.FilterChainImpl;
import com.alibaba.druid.mock.MockDriver;
import com.alibaba.druid.pool.DruidPooledPreparedStatement.PreparedStatementKey;
import com.alibaba.druid.pool.vendor.*;
import com.alibaba.druid.proxy.DruidDriver;
import com.alibaba.druid.proxy.jdbc.DataSourceProxyConfig;
import com.alibaba.druid.proxy.jdbc.TransactionInfo;
import com.alibaba.druid.sql.ast.SQLStatement;
import com.alibaba.druid.sql.ast.statement.SQLSelectQuery;
import com.alibaba.druid.sql.ast.statement.SQLSelectQueryBlock;
import com.alibaba.druid.sql.ast.statement.SQLSelectStatement;
import com.alibaba.druid.sql.parser.SQLParserUtils;
import com.alibaba.druid.sql.parser.SQLStatementParser;
import com.alibaba.druid.stat.DruidDataSourceStatManager;
import com.alibaba.druid.stat.JdbcDataSourceStat;
import com.alibaba.druid.stat.JdbcSqlStat;
import com.alibaba.druid.stat.JdbcSqlStatValue;
import com.alibaba.druid.support.logging.Log;
import com.alibaba.druid.support.logging.LogFactory;
import com.alibaba.druid.util.JMXUtils;
import com.alibaba.druid.util.JdbcConstants;
import com.alibaba.druid.util.JdbcUtils;
import com.alibaba.druid.util.StringUtils;
import com.alibaba.druid.util.Utils;
import com.alibaba.druid.wall.WallFilter;
import com.alibaba.druid.wall.WallProviderStatValue;

/**
 * @author ljw [ljw2083@alibaba-inc.com]
 * @author wenshao [szujobs@hotmail.com]
 */
public class DruidDataSource extends DruidAbstractDataSource implements DruidDataSourceMBean, ManagedDataSource, Referenceable, Closeable, Cloneable, ConnectionPoolDataSource, MBeanRegistration {

    private final static Log LOG = LogFactory.getLog(DruidDataSource.class);
    private static final long serialVersionUID = 1L;
    // stats
    private volatile long recycleErrorCount = 0L;
    private long connectCount = 0L;
    private long closeCount = 0L;
    private volatile long connectErrorCount = 0L;
    private long recycleCount = 0L;
    private long removeAbandonedCount = 0L;
    private long notEmptyWaitCount = 0L;
    private long notEmptySignalCount = 0L;
    private long notEmptyWaitNanos = 0L;
    private int keepAliveCheckCount = 0;
    private int activePeak = 0;
    private long activePeakTime = 0;
    //空闲连接池数量峰值
    private int poolingPeak = 0;
    private long poolingPeakTime = 0;
    // store 存储空闲Connection
    private volatile DruidConnectionHolder[] connections;
    // 指的是connections中的Connection数量，指的是空闲连接数量
    private int poolingCount = 0;
    // 活跃Connection数量
    private int activeCount = 0;
    // 丢弃的Connection数量
    private volatile long discardCount = 0;
    //处于等待中的消费者线程数量
    private int notEmptyWaitThreadCount = 0;
    private int notEmptyWaitThreadPeak = 0;
    // 存储待删除的Connection
    private DruidConnectionHolder[] evictConnections;
    // 存储活跃Connection
    private DruidConnectionHolder[] keepAliveConnections;

    // threads
    private volatile ScheduledFuture<?> destroySchedulerFuture;
    private DestroyTask destroyTask;

    private volatile Future<?> createSchedulerFuture;

    private CreateConnectionThread createConnectionThread;
    private DestroyConnectionThread destroyConnectionThread;
    private LogStatsThread logStatsThread;
    private int createTaskCount;

    private volatile long createTaskIdSeed = 1L;
    private long[] createTasks;

    private final CountDownLatch initedLatch = new CountDownLatch(2);

    private volatile boolean enable = true;

    private boolean resetStatEnable = true;
    private volatile long resetCount = 0L;

    private String initStackTrace;

    private volatile boolean closing = false;
    private volatile boolean closed = false;
    private long closeTimeMillis = -1L;

    protected JdbcDataSourceStat dataSourceStat;

    private boolean useGlobalDataSourceStat = false;
    private boolean mbeanRegistered = false;
    public static ThreadLocal<Long> waitNanosLocal = new ThreadLocal<Long>();
    private boolean logDifferentThread = true;
    private volatile boolean keepAlive = false;
    private boolean asyncInit = false;
    protected boolean killWhenSocketReadTimeout = false;
    protected boolean checkExecuteTime = false;

    private static List<Filter> autoFilters = null;
    private boolean loadSpifilterSkip = false;
    private volatile DataSourceDisableException disableException = null;

    protected static final AtomicLongFieldUpdater<DruidDataSource> recycleErrorCountUpdater = AtomicLongFieldUpdater
            .newUpdater(DruidDataSource.class, "recycleErrorCount");
    protected static final AtomicLongFieldUpdater<DruidDataSource> connectErrorCountUpdater = AtomicLongFieldUpdater
            .newUpdater(DruidDataSource.class, "connectErrorCount");
    protected static final AtomicLongFieldUpdater<DruidDataSource> resetCountUpdater = AtomicLongFieldUpdater
            .newUpdater(DruidDataSource.class, "resetCount");
    protected static final AtomicLongFieldUpdater<DruidDataSource> createTaskIdSeedUpdater = AtomicLongFieldUpdater
            .newUpdater(DruidDataSource.class, "createTaskIdSeed");

    public DruidDataSource() {
        this(false);
    }

    public DruidDataSource(boolean fairLock) {
        super(fairLock);

        //使用命令行配置更新数据源
        configFromPropety(System.getProperties());
    }

    public boolean isAsyncInit() {
        return asyncInit;
    }

    public void setAsyncInit(boolean asyncInit) {
        this.asyncInit = asyncInit;
    }

    public void configFromPropety(Properties properties) {
        {
            String property = properties.getProperty("druid.name");
            if (property != null) {
                this.setName(property);
            }
        }
        {
            String property = properties.getProperty("druid.url");
            if (property != null) {
                this.setUrl(property);
            }
        }
        {
            String property = properties.getProperty("druid.username");
            if (property != null) {
                this.setUsername(property);
            }
        }
        {
            String property = properties.getProperty("druid.password");
            if (property != null) {
                this.setPassword(property);
            }
        }
        {
            Boolean value = getBoolean(properties, "druid.testWhileIdle");
            if (value != null) {
                this.testWhileIdle = value;
            }
        }
        {
            Boolean value = getBoolean(properties, "druid.testOnBorrow");
            if (value != null) {
                this.testOnBorrow = value;
            }
        }
        {
            String property = properties.getProperty("druid.validationQuery");
            if (property != null && property.length() > 0) {
                this.setValidationQuery(property);
            }
        }
        {
            Boolean value = getBoolean(properties, "druid.useGlobalDataSourceStat");
            if (value != null) {
                this.setUseGlobalDataSourceStat(value);
            }
        }
        {
            Boolean value = getBoolean(properties, "druid.useGloalDataSourceStat"); // compatible for early versions
            if (value != null) {
                this.setUseGlobalDataSourceStat(value);
            }
        }
        {
            Boolean value = getBoolean(properties, "druid.asyncInit"); // compatible for early versions
            if (value != null) {
                this.setAsyncInit(value);
            }
        }
        {
            String property = properties.getProperty("druid.filters");

            if (property != null && property.length() > 0) {
                try {
                    this.setFilters(property);
                } catch (SQLException e) {
                    LOG.error("setFilters error", e);
                }
            }
        }
        {
            String property = properties.getProperty(Constants.DRUID_TIME_BETWEEN_LOG_STATS_MILLIS);
            if (property != null && property.length() > 0) {
                try {
                    long value = Long.parseLong(property);
                    this.setTimeBetweenLogStatsMillis(value);
                } catch (NumberFormatException e) {
                    LOG.error("illegal property '" + Constants.DRUID_TIME_BETWEEN_LOG_STATS_MILLIS + "'", e);
                }
            }
        }
        {
            String property = properties.getProperty(Constants.DRUID_STAT_SQL_MAX_SIZE);
            if (property != null && property.length() > 0) {
                try {
                    int value = Integer.parseInt(property);
                    if (dataSourceStat != null) {
                        dataSourceStat.setMaxSqlSize(value);
                    }
                } catch (NumberFormatException e) {
                    LOG.error("illegal property '" + Constants.DRUID_STAT_SQL_MAX_SIZE + "'", e);
                }
            }
        }
        {
            Boolean value = getBoolean(properties, "druid.clearFiltersEnable");
            if (value != null) {
                this.setClearFiltersEnable(value);
            }
        }
        {
            Boolean value = getBoolean(properties, "druid.resetStatEnable");
            if (value != null) {
                this.setResetStatEnable(value);
            }
        }
        {
            String property = properties.getProperty("druid.notFullTimeoutRetryCount");
            if (property != null && property.length() > 0) {
                try {
                    int value = Integer.parseInt(property);
                    this.setNotFullTimeoutRetryCount(value);
                } catch (NumberFormatException e) {
                    LOG.error("illegal property 'druid.notFullTimeoutRetryCount'", e);
                }
            }
        }
        {
            String property = properties.getProperty("druid.timeBetweenEvictionRunsMillis");
            if (property != null && property.length() > 0) {
                try {
                    long value = Long.parseLong(property);
                    this.setTimeBetweenEvictionRunsMillis(value);
                } catch (NumberFormatException e) {
                    LOG.error("illegal property 'druid.timeBetweenEvictionRunsMillis'", e);
                }
            }
        }
        {
            String property = properties.getProperty("druid.maxWaitThreadCount");
            if (property != null && property.length() > 0) {
                try {
                    int value = Integer.parseInt(property);
                    this.setMaxWaitThreadCount(value);
                } catch (NumberFormatException e) {
                    LOG.error("illegal property 'druid.maxWaitThreadCount'", e);
                }
            }
        }
        {
            String property = properties.getProperty("druid.maxWait");
            if (property != null && property.length() > 0) {
                try {
                    int value = Integer.parseInt(property);
                    this.setMaxWait(value);
                } catch (NumberFormatException e) {
                    LOG.error("illegal property 'druid.maxWait'", e);
                }
            }
        }
        {
            Boolean value = getBoolean(properties, "druid.failFast");
            if (value != null) {
                this.setFailFast(value);
            }
        }
        {
            String property = properties.getProperty("druid.phyTimeoutMillis");
            if (property != null && property.length() > 0) {
                try {
                    long value = Long.parseLong(property);
                    this.setPhyTimeoutMillis(value);
                } catch (NumberFormatException e) {
                    LOG.error("illegal property 'druid.phyTimeoutMillis'", e);
                }
            }
        }
        {
            String property = properties.getProperty("druid.phyMaxUseCount");
            if (property != null && property.length() > 0) {
                try {
                    long value = Long.parseLong(property);
                    this.setPhyMaxUseCount(value);
                } catch (NumberFormatException e) {
                    LOG.error("illegal property 'druid.phyMaxUseCount'", e);
                }
            }
        }
        {
            String property = properties.getProperty("druid.minEvictableIdleTimeMillis");
            if (property != null && property.length() > 0) {
                try {
                    long value = Long.parseLong(property);
                    this.setMinEvictableIdleTimeMillis(value);
                } catch (NumberFormatException e) {
                    LOG.error("illegal property 'druid.minEvictableIdleTimeMillis'", e);
                }
            }
        }
        {
            String property = properties.getProperty("druid.maxEvictableIdleTimeMillis");
            if (property != null && property.length() > 0) {
                try {
                    long value = Long.parseLong(property);
                    this.setMaxEvictableIdleTimeMillis(value);
                } catch (NumberFormatException e) {
                    LOG.error("illegal property 'druid.maxEvictableIdleTimeMillis'", e);
                }
            }
        }
        {
            Boolean value = getBoolean(properties, "druid.keepAlive");
            if (value != null) {
                this.setKeepAlive(value);
            }
        }
        {
            String property = properties.getProperty("druid.keepAliveBetweenTimeMillis");
            if (property != null && property.length() > 0) {
                try {
                    long value = Long.parseLong(property);
                    this.setKeepAliveBetweenTimeMillis(value);
                } catch (NumberFormatException e) {
                    LOG.error("illegal property 'druid.keepAliveBetweenTimeMillis'", e);
                }
            }
        }
        {
            Boolean value = getBoolean(properties, "druid.poolPreparedStatements");
            if (value != null) {
                this.setPoolPreparedStatements0(value);
            }
        }
        {
            Boolean value = getBoolean(properties, "druid.initVariants");
            if (value != null) {
                this.setInitVariants(value);
            }
        }
        {
            Boolean value = getBoolean(properties, "druid.initGlobalVariants");
            if (value != null) {
                this.setInitGlobalVariants(value);
            }
        }
        {
            Boolean value = getBoolean(properties, "druid.useUnfairLock");
            if (value != null) {
                this.setUseUnfairLock(value);
            }
        }
        {
            String property = properties.getProperty("druid.driverClassName");
            if (property != null) {
                this.setDriverClassName(property);
            }
        }
        {
            String property = properties.getProperty("druid.initialSize");
            if (property != null && property.length() > 0) {
                try {
                    int value = Integer.parseInt(property);
                    this.setInitialSize(value);
                } catch (NumberFormatException e) {
                    LOG.error("illegal property 'druid.initialSize'", e);
                }
            }
        }
        {
            String property = properties.getProperty("druid.minIdle");
            if (property != null && property.length() > 0) {
                try {
                    int value = Integer.parseInt(property);
                    this.setMinIdle(value);
                } catch (NumberFormatException e) {
                    LOG.error("illegal property 'druid.minIdle'", e);
                }
            }
        }
        {
            String property = properties.getProperty("druid.maxActive");
            if (property != null && property.length() > 0) {
                try {
                    int value = Integer.parseInt(property);
                    this.setMaxActive(value);
                } catch (NumberFormatException e) {
                    LOG.error("illegal property 'druid.maxActive'", e);
                }
            }
        }
        {
            Boolean value = getBoolean(properties, "druid.killWhenSocketReadTimeout");
            if (value != null) {
                setKillWhenSocketReadTimeout(value);
            }
        }
        {
            String property = properties.getProperty("druid.connectProperties");
            if (property != null) {
                this.setConnectionProperties(property);
            }
        }
        {
            String property = properties.getProperty("druid.maxPoolPreparedStatementPerConnectionSize");
            if (property != null && property.length() > 0) {
                try {
                    int value = Integer.parseInt(property);
                    this.setMaxPoolPreparedStatementPerConnectionSize(value);
                } catch (NumberFormatException e) {
                    LOG.error("illegal property 'druid.maxPoolPreparedStatementPerConnectionSize'", e);
                }
            }
        }
        {
            String property = properties.getProperty("druid.initConnectionSqls");
            if (property != null && property.length() > 0) {
                try {
                    StringTokenizer tokenizer = new StringTokenizer(property, ";");
                    setConnectionInitSqls(Collections.list(tokenizer));
                } catch (NumberFormatException e) {
                    LOG.error("illegal property 'druid.initConnectionSqls'", e);
                }
            }
        }
        {
            String property = System.getProperty("druid.load.spifilter.skip");
            if (property != null && !"false".equals(property)) {
                loadSpifilterSkip = true;
            }
        }
        {
            String property = System.getProperty("druid.checkExecuteTime");
            if (property != null && !"false".equals(property)) {
                checkExecuteTime = true;
            }
        }
    }

    public boolean isKillWhenSocketReadTimeout() {
        return killWhenSocketReadTimeout;
    }

    public void setKillWhenSocketReadTimeout(boolean killWhenSocketTimeOut) {
        this.killWhenSocketReadTimeout = killWhenSocketTimeOut;
    }

    public boolean isUseGlobalDataSourceStat() {
        return useGlobalDataSourceStat;
    }

    public void setUseGlobalDataSourceStat(boolean useGlobalDataSourceStat) {
        this.useGlobalDataSourceStat = useGlobalDataSourceStat;
    }

    public boolean isKeepAlive() {
        return keepAlive;
    }

    public void setKeepAlive(boolean keepAlive) {
        this.keepAlive = keepAlive;
    }

    public String getInitStackTrace() {
        return initStackTrace;
    }

    public boolean isResetStatEnable() {
        return resetStatEnable;
    }

    public void setResetStatEnable(boolean resetStatEnable) {
        this.resetStatEnable = resetStatEnable;
        if (dataSourceStat != null) {
            dataSourceStat.setResetStatEnable(resetStatEnable);
        }
    }

    public long getDiscardCount() {
        return discardCount;
    }

    public void restart() throws SQLException {
        lock.lock();
        try {
            if (activeCount > 0) {
                throw new SQLException("can not restart, activeCount not zero. " + activeCount);
            }
            if (LOG.isInfoEnabled()) {
                LOG.info("{dataSource-" + this.getID() + "} restart");
            }

            this.close();
            this.resetStat();
            this.inited = false;
            this.enable = true;
            this.closed = false;
        } finally {
            lock.unlock();
        }
    }

    public void resetStat() {
        if (!isResetStatEnable()) {
            return;
        }

        lock.lock();
        try {
            connectCount = 0;
            closeCount = 0;
            discardCount = 0;
            recycleCount = 0;
            createCount = 0L;
            directCreateCount = 0;
            destroyCount = 0L;
            removeAbandonedCount = 0;
            notEmptyWaitCount = 0;
            notEmptySignalCount = 0L;
            notEmptyWaitNanos = 0;

            activePeak = activeCount;
            activePeakTime = 0;
            poolingPeak = 0;
            createTimespan = 0;
            lastError = null;
            lastErrorTimeMillis = 0;
            lastCreateError = null;
            lastCreateErrorTimeMillis = 0;
        } finally {
            lock.unlock();
        }

        connectErrorCountUpdater.set(this, 0);
        errorCountUpdater.set(this, 0);
        commitCountUpdater.set(this, 0);
        rollbackCountUpdater.set(this, 0);
        startTransactionCountUpdater.set(this, 0);
        cachedPreparedStatementHitCountUpdater.set(this, 0);
        closedPreparedStatementCountUpdater.set(this, 0);
        preparedStatementCountUpdater.set(this, 0);
        transactionHistogram.reset();
        cachedPreparedStatementDeleteCountUpdater.set(this, 0);
        recycleErrorCountUpdater.set(this, 0);

        resetCountUpdater.incrementAndGet(this);
    }

    public long getResetCount() {
        return this.resetCount;
    }

    public boolean isEnable() {
        return enable;
    }

    public void setEnable(boolean enable) {
        lock.lock();
        try {
            this.enable = enable;
            if (!enable) {
                notEmpty.signalAll();
                notEmptySignalCount++;
            }
        } finally {
            lock.unlock();
        }
    }

    public void setPoolPreparedStatements(boolean value) {
        setPoolPreparedStatements0(value);
    }

    private void setPoolPreparedStatements0(boolean value) {
        if (this.poolPreparedStatements == value) {
            return;
        }

        this.poolPreparedStatements = value;

        if (!inited) {
            return;
        }

        if (LOG.isInfoEnabled()) {
            LOG.info("set poolPreparedStatements " + this.poolPreparedStatements + " -> " + value);
        }

        if (!value) {
            lock.lock();
            try {

                for (int i = 0; i < poolingCount; ++i) {
                    DruidConnectionHolder connection = connections[i];

                    for (PreparedStatementHolder holder : connection.getStatementPool()
                            .getMap()
                            .values()) {
                        closePreapredStatement(holder);
                    }

                    connection.getStatementPool().getMap().clear();
                }
            } finally {
                lock.unlock();
            }
        }
    }

    public void setMaxActive(int maxActive) {
        if (this.maxActive == maxActive) {
            return;
        }

        if (maxActive == 0) {
            throw new IllegalArgumentException("maxActive can't not set zero");
        }

        if (!inited) {
            this.maxActive = maxActive;
            return;
        }

        if (maxActive < this.minIdle) {
            throw new IllegalArgumentException("maxActive less than minIdle, " + maxActive + " < " + this.minIdle);
        }

        if (LOG.isInfoEnabled()) {
            LOG.info("maxActive changed : " + this.maxActive + " -> " + maxActive);
        }

        lock.lock();
        try {
            int allCount = this.poolingCount + this.activeCount;

            if (maxActive > allCount) {
                this.connections = Arrays.copyOf(this.connections, maxActive);
                evictConnections = new DruidConnectionHolder[maxActive];
                keepAliveConnections = new DruidConnectionHolder[maxActive];
            } else {
                this.connections = Arrays.copyOf(this.connections, allCount);
                evictConnections = new DruidConnectionHolder[allCount];
                keepAliveConnections = new DruidConnectionHolder[allCount];
            }

            this.maxActive = maxActive;
        } finally {
            lock.unlock();
        }
    }

    @SuppressWarnings("rawtypes")
    public void setConnectProperties(Properties properties) {
        if (properties == null) {
            properties = new Properties();
        }

        boolean equals;
        if (properties.size() == this.connectProperties.size()) {
            equals = true;
            for (Map.Entry entry : properties.entrySet()) {
                Object value = this.connectProperties.get(entry.getKey());
                Object entryValue = entry.getValue();
                if (value == null && entryValue != null) {
                    equals = false;
                    break;
                }

                if (!value.equals(entry.getValue())) {
                    equals = false;
                    break;
                }
            }
        } else {
            equals = false;
        }

        if (!equals) {
            if (inited && LOG.isInfoEnabled()) {
                LOG.info("connectProperties changed : " + this.connectProperties + " -> " + properties);
            }

            configFromPropety(properties);

            for (Filter filter : this.filters) {
                filter.configFromProperties(properties);
            }

            if (exceptionSorter != null) {
                exceptionSorter.configFromProperties(properties);
            }

            if (validConnectionChecker != null) {
                validConnectionChecker.configFromProperties(properties);
            }

            if (statLogger != null) {
                statLogger.configFromProperties(properties);
            }
        }

        this.connectProperties = properties;
    }

    public void init() throws SQLException {
        if (inited) {
            //已完成初始化，返回
            return;
        }

        //考虑到并发初始化，这里要考虑多线程初始化导致的死锁，使用静态初始化
        // bug fixed for dead lock, for issue #2980
        DruidDriver.getInstance();

        //初始化时构造函数创建的对象级锁。
        //该锁对象被多个线程持有，包括创建连接线程、销毁连接线程、put连接线程、get连接线程等。
        //该锁的作用有：
        //  1.开始时，DataSource初始化的时候，此时其他线程还不存在，一定是DataSource初始化线程持有锁，在初始化完成后才会释放锁。
        //     这样就保证了，只有在DataSource初始化完成后，才可以创建和销毁Connection，即连接不会先于连接池创建。
        final ReentrantLock lock = this.lock;
        try {
            lock.lockInterruptibly();
        } catch (InterruptedException e) {
            throw new SQLException("interrupt", e);
        }

        boolean init = false;
        try {
            if (inited) {
                return;
            }

            //保留开始初始化时的堆栈信息
            initStackTrace = Utils.toString(Thread.currentThread().getStackTrace());

            //AtomicInteger 从0开始自增，最小为1
            this.id = DruidDriver.createDataSourceId();
            if (this.id > 1) {
                //多DataSource的情况，分开每个DataSource和它创建关联的连接、statement、resultset、transaction的id
                //如果DataSource的id是3，10万到20万之内的id就都是这个DataSource的
                long delta = (this.id - 1) * 100000;
                this.connectionIdSeedUpdater.addAndGet(this, delta);
                this.statementIdSeedUpdater.addAndGet(this, delta);
                this.resultSetIdSeedUpdater.addAndGet(this, delta);
                this.transactionIdSeedUpdater.addAndGet(this, delta);
            }

            if (this.jdbcUrl != null) {
                this.jdbcUrl = this.jdbcUrl.trim();
                initFromWrapDriverUrl();
            }

            for (Filter filter : filters) {
                //为过滤器传入代理连接池对象
                filter.init(this);
            }

            if (this.dbType == null || this.dbType.length() == 0) {
                this.dbType = JdbcUtils.getDbType(jdbcUrl, null);
            }

            if (JdbcConstants.MYSQL.equals(this.dbType) || JdbcConstants.MARIADB.equals(this.dbType) || JdbcConstants.OCEANBASE
                    .equals(this.dbType) || JdbcConstants.ALIYUN_ADS.equals(this.dbType)) {
                boolean cacheServerConfigurationSet = false;
                if (this.connectProperties.containsKey("cacheServerConfiguration")) {
                    cacheServerConfigurationSet = true;
                } else if (this.jdbcUrl.indexOf("cacheServerConfiguration") != -1) {
                    cacheServerConfigurationSet = true;
                }
                if (cacheServerConfigurationSet) {
                    this.connectProperties.put("cacheServerConfiguration", "true");
                }
            }

            if (maxActive <= 0) {
                throw new IllegalArgumentException("illegal maxActive " + maxActive);
            }

            if (maxActive < minIdle) {
                throw new IllegalArgumentException("illegal maxActive " + maxActive);
            }

            if (getInitialSize() > maxActive) {
                throw new IllegalArgumentException("illegal initialSize " + this.initialSize + ", maxActive " + maxActive);
            }

            if (timeBetweenLogStatsMillis > 0 && useGlobalDataSourceStat) {
                throw new IllegalArgumentException("timeBetweenLogStatsMillis not support useGlobalDataSourceStat=true");
            }

            if (maxEvictableIdleTimeMillis < minEvictableIdleTimeMillis) {
                throw new SQLException("maxEvictableIdleTimeMillis must be grater than minEvictableIdleTimeMillis");
            }

            if (this.driverClass != null) {
                this.driverClass = driverClass.trim();
            }

            //SPI加载Filter，主要加载标注了@AutoLoad注解的
            initFromSPIServiceLoader();

            //解析Driver类型
            resolveDriver();

            initCheck();

            initExceptionSorter();
            //连接是否有效检查器
            initValidConnectionChecker();
            //查询是否有效检查器
            validationQueryCheck();

            if (isUseGlobalDataSourceStat()) {
                //使用全局的数据源状态bean
                dataSourceStat = JdbcDataSourceStat.getGlobal();
                if (dataSourceStat == null) {
                    dataSourceStat = new JdbcDataSourceStat("Global", "Global", this.dbType);
                    JdbcDataSourceStat.setGlobal(dataSourceStat);
                }
                if (dataSourceStat.getDbType() == null) {
                    dataSourceStat.setDbType(this.dbType);
                }
            } else {
                //当前DataSource私有的数据源状态Bean
                dataSourceStat = new JdbcDataSourceStat(this.name, this.jdbcUrl, this.dbType, this.connectProperties);
            }
            //是否可以重置统计状态
            dataSourceStat.setResetStatEnable(this.resetStatEnable);

            //空闲连接池
            connections = new DruidConnectionHolder[maxActive];
            //待删除连接池
            evictConnections = new DruidConnectionHolder[maxActive];
            //保活连接池
            keepAliveConnections = new DruidConnectionHolder[maxActive];

            //创建Connection错误
            SQLException connectError = null;

            if (createScheduler != null && asyncInit) {
                //异步初始化Connection
                for (int i = 0; i < initialSize; ++i) {
                    //提交创建连接任务
                    submitCreateTask(true);
                }
            } else if (!asyncInit) {
                // init connections
                //因为是连接池初始化，目前不存在活跃的连接，所以空闲连接池数量poolingCount=已有的连接总数量
                //根据配置的initialSize数量，初始化Connnection，放入空闲连接池
                while (poolingCount < initialSize) {
                    //poolingCount是连接池内已经有的所有Connection数量
                    //initialSize配置的初始化数量
                    try {
                        //创建Connection，可能是原始对象，可能是代理对象。根据配置进行Connnection的初始化和有效校验。
                        //PhysicalConnectionInfo就是用来封装一个Connection和它的各种状态等信息，减少传参的参数数量
                        PhysicalConnectionInfo pyConnectInfo = createPhysicalConnection();
                        //持有当前连接池对象和刚创建成功的1个连接对象，不是所有的连接对象
                        DruidConnectionHolder holder = new DruidConnectionHolder(this, pyConnectInfo);
                        //放入连接池
                        connections[poolingCount++] = holder;
                    } catch (SQLException ex) {
                        LOG.error("init datasource error, url: " + this.getUrl(), ex);
                        if (initExceptionThrow) {
                            connectError = ex;
                            break;
                        } else {
                            //忽略异常，睡眠3秒
                            Thread.sleep(3000);
                        }
                    }
                }

                if (poolingCount > 0) {
                    //更新空闲连接池数量峰值
                    poolingPeak = poolingCount;
                    poolingPeakTime = System.currentTimeMillis();
                }
            }

            //创建和启动连接池状态统计日志线程，固定间隔时间收集统计数据，打印日志。
            createAndLogThread();
            //创建和启动Connection创建线程，持有initedLatch
            createAndStartCreatorThread();
            //创建和启动Connection销毁线程，持有initedLatch
            createAndStartDestroyThread();

            //initedLatch==2。主线程阻塞，等待Connection创建和销毁线程初始化和运行起来
            initedLatch.await();
            //初始化完成
            init = true;

            initedTime = new Date();
            //jmx 注册DruidDataSource MBean
            registerMbean();

            if (connectError != null && poolingCount == 0) {
                //连接异常 并且 一个连接也没创建出来 应该说是一个有效的连接也没创建出来，
                //证明可能是网络、数据库地址、用户名、密码等有问题
                throw connectError;
            }

            if (keepAlive) {
                //因为配置的最小空闲连接数，这里要创建连接达到这个要求
                // async fill to minIdle
                if (createScheduler != null) {
                    //异步初始化
                    for (int i = 0; i < minIdle; ++i) {
                        //提交连接创建任务
                        submitCreateTask(true);
                    }
                } else {
                    //同步初始化，唤醒生产者线程，创建连接
                    this.emptySignal();
                }
            }

        } catch (SQLException e) {
            LOG.error("{dataSource-" + this.getID() + "} init error", e);
            throw e;
        } catch (InterruptedException e) {
            throw new SQLException(e.getMessage(), e);
        } catch (RuntimeException e) {
            LOG.error("{dataSource-" + this.getID() + "} init error", e);
            throw e;
        } catch (Error e) {
            LOG.error("{dataSource-" + this.getID() + "} init error", e);
            throw e;

        } finally {
            //DataSource完成初始化，释放锁，打info日志
            inited = true;
            lock.unlock();

            if (init && LOG.isInfoEnabled()) {
                String msg = "{dataSource-" + this.getID();

                if (this.name != null && !this.name.isEmpty()) {
                    msg += ",";
                    msg += this.name;
                }

                msg += "} inited";

                LOG.info(msg);
            }
        }
    }

    private void submitCreateTask(boolean initTask) {
        createTaskCount++;
        CreateConnectionTask task = new CreateConnectionTask(initTask);
        if (createTasks == null) {
            createTasks = new long[8];
        }

        boolean putted = false;
        for (int i = 0; i < createTasks.length; ++i) {
            if (createTasks[i] == 0) {
                createTasks[i] = task.taskId;
                putted = true;
                break;
            }
        }
        if (!putted) {
            long[] array = new long[createTasks.length * 3 / 2];
            System.arraycopy(createTasks, 0, array, 0, createTasks.length);
            array[createTasks.length] = task.taskId;
            createTasks = array;
        }

        this.createSchedulerFuture = createScheduler.submit(task);
    }

    private boolean clearCreateTask(long taskId) {
        if (createTasks == null) {
            return false;
        }

        if (taskId == 0) {
            return false;
        }

        for (int i = 0; i < createTasks.length; i++) {
            if (createTasks[i] == taskId) {
                createTasks[i] = 0;
                createTaskCount--;

                if (createTaskCount < 0) {
                    createTaskCount = 0;
                }

                if (createTaskCount == 0 && createTasks.length > 8) {
                    createTasks = new long[8];
                }
                return true;
            }
        }

        if (LOG.isWarnEnabled()) {
            LOG.warn("clear create task failed : " + taskId);
        }

        return false;
    }

    private void createAndLogThread() {
        if (this.timeBetweenLogStatsMillis <= 0) {
            //日志统计间隔时间，没配置的话就不创建日志线程
            return;
        }

        String threadName = "Druid-ConnectionPool-Log-" + System.identityHashCode(this);
        logStatsThread = new LogStatsThread(threadName);
        //启动日志统计线程
        logStatsThread.start();

        this.resetStatEnable = false;
    }

    protected void createAndStartDestroyThread() {
        destroyTask = new DestroyTask();

        if (destroyScheduler != null) {
            long period = timeBetweenEvictionRunsMillis;
            if (period <= 0) {
                period = 1000;
            }
            destroySchedulerFuture = destroyScheduler.scheduleAtFixedRate(destroyTask, period, period, TimeUnit.MILLISECONDS);
            initedLatch.countDown();
            return;
        }

        String threadName = "Druid-ConnectionPool-Destroy-" + System.identityHashCode(this);
        destroyConnectionThread = new DestroyConnectionThread(threadName);
        destroyConnectionThread.start();
    }

    protected void createAndStartCreatorThread() {
        if (createScheduler == null) {
            //同步初始化
            String threadName = "Druid-ConnectionPool-Create-" + System.identityHashCode(this);
            createConnectionThread = new CreateConnectionThread(threadName);
            createConnectionThread.start();
            return;
        }

        //异步初始化，initedLatch-1，执行DataSource初始化的主线程阻塞在CountDownLatch，在等待继续执行
        initedLatch.countDown();
    }

    /**
     * load filters from SPI ServiceLoader
     * @see ServiceLoader
     */
    private void initFromSPIServiceLoader() {
        if (loadSpifilterSkip) {
            return;
        }

        if (autoFilters == null) {
            List<Filter> filters = new ArrayList<Filter>();
            ServiceLoader<Filter> autoFilterLoader = ServiceLoader.load(Filter.class);

            for (Filter filter : autoFilterLoader) {
                AutoLoad autoLoad = filter.getClass().getAnnotation(AutoLoad.class);
                if (autoLoad != null && autoLoad.value()) {
                    filters.add(filter);
                }
            }
            autoFilters = filters;
        }

        for (Filter filter : autoFilters) {
            if (LOG.isInfoEnabled()) {
                LOG.info("load filter from spi :" + filter.getClass().getName());
            }
            addFilter(filter);
        }
    }

    private void initFromWrapDriverUrl() throws SQLException {
        if (!jdbcUrl.startsWith(DruidDriver.DEFAULT_PREFIX)) {
            return;
        }

        DataSourceProxyConfig config = DruidDriver.parseConfig(jdbcUrl, null);
        this.driverClass = config.getRawDriverClassName();

        LOG.error("error url : '" + jdbcUrl + "', it should be : '" + config.getRawUrl() + "'");

        this.jdbcUrl = config.getRawUrl();
        if (this.name == null) {
            this.name = config.getName();
        }

        for (Filter filter : config.getFilters()) {
            addFilter(filter);
        }
    }

    /**
     * 会去重复
     * @param filter
     */
    private void addFilter(Filter filter) {
        boolean exists = false;
        for (Filter initedFilter : this.filters) {
            if (initedFilter.getClass() == filter.getClass()) {
                exists = true;
                break;
            }
        }

        if (!exists) {
            filter.init(this);
            this.filters.add(filter);
        }

    }

    private void validationQueryCheck() {
        if (!(testOnBorrow || testOnReturn || testWhileIdle)) {
            return;
        }

        if (this.validConnectionChecker != null) {
            return;
        }

        if (this.validationQuery != null && this.validationQuery.length() > 0) {
            return;
        }

        String errorMessage = "";

        if (testOnBorrow) {
            errorMessage += "testOnBorrow is true, ";
        }

        if (testOnReturn) {
            errorMessage += "testOnReturn is true, ";
        }

        if (testWhileIdle) {
            errorMessage += "testWhileIdle is true, ";
        }

        LOG.error(errorMessage + "validationQuery not set");
    }

    protected void resolveDriver() throws SQLException {
        if (this.driver == null) {
            if (this.driverClass == null || this.driverClass.isEmpty()) {
                this.driverClass = JdbcUtils.getDriverClassName(this.jdbcUrl);
            }

            if (MockDriver.class.getName().equals(driverClass)) {
                driver = MockDriver.instance;
            } else {
                if (jdbcUrl == null && (driverClass == null || driverClass.length() == 0)) {
                    throw new SQLException("url not set");
                }
                driver = JdbcUtils.createDriver(driverClassLoader, driverClass);
            }
        } else {
            if (this.driverClass == null) {
                this.driverClass = driver.getClass().getName();
            }
        }
    }

    protected void initCheck() throws SQLException {
        if (JdbcUtils.ORACLE.equals(this.dbType)) {
            isOracle = true;

            if (driver.getMajorVersion() < 10) {
                throw new SQLException("not support oracle driver " + driver.getMajorVersion() + "." + driver
                        .getMinorVersion());
            }

            if (driver.getMajorVersion() == 10 && isUseOracleImplicitCache()) {
                this.getConnectProperties()
                        .setProperty("oracle.jdbc.FreeMemoryOnEnterImplicitCache", "true");
            }

            oracleValidationQueryCheck();
        } else if (JdbcUtils.DB2.equals(dbType)) {
            db2ValidationQueryCheck();
        } else if (JdbcUtils.MYSQL.equals(this.dbType) || JdbcUtils.MYSQL_DRIVER_6.equals(this.dbType)) {
            isMySql = true;
        }

        if (removeAbandoned) {
            LOG.warn("removeAbandoned is true, not use in production.");
        }
    }

    private void oracleValidationQueryCheck() {
        if (validationQuery == null) {
            return;
        }
        if (validationQuery.length() == 0) {
            return;
        }

        SQLStatementParser sqlStmtParser = SQLParserUtils.createSQLStatementParser(validationQuery, this.dbType);
        List<SQLStatement> stmtList = sqlStmtParser.parseStatementList();

        if (stmtList.size() != 1) {
            return;
        }

        SQLStatement stmt = stmtList.get(0);
        if (!(stmt instanceof SQLSelectStatement)) {
            return;
        }

        SQLSelectQuery query = ((SQLSelectStatement) stmt).getSelect().getQuery();
        if (query instanceof SQLSelectQueryBlock) {
            if (((SQLSelectQueryBlock) query).getFrom() == null) {
                LOG.error("invalid oracle validationQuery. " + validationQuery + ", may should be : " + validationQuery + " FROM DUAL");
            }
        }
    }

    private void db2ValidationQueryCheck() {
        if (validationQuery == null) {
            return;
        }
        if (validationQuery.length() == 0) {
            return;
        }

        SQLStatementParser sqlStmtParser = SQLParserUtils.createSQLStatementParser(validationQuery, this.dbType);
        List<SQLStatement> stmtList = sqlStmtParser.parseStatementList();

        if (stmtList.size() != 1) {
            return;
        }

        SQLStatement stmt = stmtList.get(0);
        if (!(stmt instanceof SQLSelectStatement)) {
            return;
        }

        SQLSelectQuery query = ((SQLSelectStatement) stmt).getSelect().getQuery();
        if (query instanceof SQLSelectQueryBlock) {
            if (((SQLSelectQueryBlock) query).getFrom() == null) {
                LOG.error("invalid db2 validationQuery. " + validationQuery + ", may should be : " + validationQuery + " FROM SYSDUMMY");
            }
        }
    }

    private void initValidConnectionChecker() {
        if (this.validConnectionChecker != null) {
            return;
        }

        String realDriverClassName = driver.getClass().getName();
        if (JdbcUtils.isMySqlDriver(realDriverClassName)) {
            this.validConnectionChecker = new MySqlValidConnectionChecker();

        } else if (realDriverClassName.equals(JdbcConstants.ORACLE_DRIVER) || realDriverClassName.equals(JdbcConstants.ORACLE_DRIVER2)) {
            this.validConnectionChecker = new OracleValidConnectionChecker();

        } else if (realDriverClassName.equals(JdbcConstants.SQL_SERVER_DRIVER) || realDriverClassName.equals(JdbcConstants.SQL_SERVER_DRIVER_SQLJDBC4) || realDriverClassName
                .equals(JdbcConstants.SQL_SERVER_DRIVER_JTDS)) {
            this.validConnectionChecker = new MSSQLValidConnectionChecker();

        } else if (realDriverClassName.equals(JdbcConstants.POSTGRESQL_DRIVER) || realDriverClassName.equals(JdbcConstants.ENTERPRISEDB_DRIVER) || realDriverClassName
                .equals(JdbcConstants.POLARDB_DRIVER)) {
            this.validConnectionChecker = new PGValidConnectionChecker();
        }
    }

    private void initExceptionSorter() {
        if (exceptionSorter instanceof NullExceptionSorter) {
            if (driver instanceof MockDriver) {
                return;
            }
        } else if (this.exceptionSorter != null) {
            return;
        }


        for (Class<?> driverClass = driver.getClass(); ; ) {
            String realDriverClassName = driverClass.getName();
            if (realDriverClassName.equals(JdbcConstants.MYSQL_DRIVER) //
                    || realDriverClassName.equals(JdbcConstants.MYSQL_DRIVER_6)) {
                this.exceptionSorter = new MySqlExceptionSorter();
                this.isMySql = true;
            } else if (realDriverClassName.equals(JdbcConstants.ORACLE_DRIVER) || realDriverClassName.equals(JdbcConstants.ORACLE_DRIVER2)) {
                this.exceptionSorter = new OracleExceptionSorter();
            } else if (realDriverClassName.equals(JdbcConstants.OCEANBASE_DRIVER)) { // 写一个真实的 TestCase
                if (JdbcUtils.OCEANBASE_ORACLE.equalsIgnoreCase(dbType)) {
                    this.exceptionSorter = new OceanBaseOracleExceptionSorter();
                } else {
                    this.exceptionSorter = new MySqlExceptionSorter();
                }
            } else if (realDriverClassName.equals("com.informix.jdbc.IfxDriver")) {
                this.exceptionSorter = new InformixExceptionSorter();

            } else if (realDriverClassName.equals("com.sybase.jdbc2.jdbc.SybDriver")) {
                this.exceptionSorter = new SybaseExceptionSorter();

            } else if (realDriverClassName.equals(JdbcConstants.POSTGRESQL_DRIVER) || realDriverClassName
                    .equals(JdbcConstants.ENTERPRISEDB_DRIVER) || realDriverClassName.equals(JdbcConstants.POLARDB_DRIVER)) {
                this.exceptionSorter = new PGExceptionSorter();

            } else if (realDriverClassName.equals("com.alibaba.druid.mock.MockDriver")) {
                this.exceptionSorter = new MockExceptionSorter();
            } else if (realDriverClassName.contains("DB2")) {
                this.exceptionSorter = new DB2ExceptionSorter();

            } else {
                Class<?> superClass = driverClass.getSuperclass();
                if (superClass != null && superClass != Object.class) {
                    driverClass = superClass;
                    continue;
                }
            }

            break;
        }
    }

    @Override
    public DruidPooledConnection getConnection() throws SQLException {
        //无超时时间，一直阻塞等待
        return getConnection(maxWait);
    }

    public DruidPooledConnection getConnection(long maxWaitMillis) throws SQLException {
        //初始化数据源
        init();

        if (filters.size() > 0) {
            //过滤器，要代理
            FilterChainImpl filterChain = new FilterChainImpl(this);
            return filterChain.dataSource_connect(this, maxWaitMillis);
        } else {
            return getConnectionDirect(maxWaitMillis);
        }
    }

    @Override
    public PooledConnection getPooledConnection() throws SQLException {
        return getConnection(maxWait);
    }

    @Override
    public PooledConnection getPooledConnection(String user, String password) throws SQLException {
        throw new UnsupportedOperationException("Not supported by DruidDataSource");
    }

    public DruidPooledConnection getConnectionDirect(long maxWaitMillis) throws SQLException {
        int notFullTimeoutRetryCnt = 0;
        for (; ; ) {
            // handle notFullTimeoutRetry
            DruidPooledConnection poolableConnection;
            try {
                poolableConnection = getConnectionInternal(maxWaitMillis);
            } catch (GetConnectionTimeoutException ex) {
                if (notFullTimeoutRetryCnt <= this.notFullTimeoutRetryCount && !isFull()) {
                    notFullTimeoutRetryCnt++;
                    if (LOG.isWarnEnabled()) {
                        LOG.warn("get connection timeout retry : " + notFullTimeoutRetryCnt);
                    }
                    continue;
                }
                throw ex;
            }

            if (testOnBorrow) {
                boolean validate = testConnectionInternal(poolableConnection.holder, poolableConnection.conn);
                if (!validate) {
                    if (LOG.isDebugEnabled()) {
                        LOG.debug("skip not validate connection.");
                    }

                    discardConnection(poolableConnection.holder);
                    continue;
                }
            } else {
                if (poolableConnection.conn.isClosed()) {
                    discardConnection(poolableConnection.holder); // 传入null，避免重复关闭
                    continue;
                }

                if (testWhileIdle) {
                    final DruidConnectionHolder holder = poolableConnection.holder;
                    long currentTimeMillis = System.currentTimeMillis();
                    long lastActiveTimeMillis = holder.lastActiveTimeMillis;
                    long lastExecTimeMillis = holder.lastExecTimeMillis;
                    long lastKeepTimeMillis = holder.lastKeepTimeMillis;

                    if (checkExecuteTime && lastExecTimeMillis != lastActiveTimeMillis) {
                        lastActiveTimeMillis = lastExecTimeMillis;
                    }

                    if (lastKeepTimeMillis > lastActiveTimeMillis) {
                        lastActiveTimeMillis = lastKeepTimeMillis;
                    }

                    long idleMillis = currentTimeMillis - lastActiveTimeMillis;

                    long timeBetweenEvictionRunsMillis = this.timeBetweenEvictionRunsMillis;

                    if (timeBetweenEvictionRunsMillis <= 0) {
                        timeBetweenEvictionRunsMillis = DEFAULT_TIME_BETWEEN_EVICTION_RUNS_MILLIS;
                    }

                    if (idleMillis >= timeBetweenEvictionRunsMillis || idleMillis < 0 // unexcepted branch
                    ) {
                        boolean validate = testConnectionInternal(poolableConnection.holder, poolableConnection.conn);
                        if (!validate) {
                            if (LOG.isDebugEnabled()) {
                                LOG.debug("skip not validate connection.");
                            }

                            discardConnection(poolableConnection.holder);
                            continue;
                        }
                    }
                }
            }

            if (removeAbandoned) {
                StackTraceElement[] stackTrace = Thread.currentThread().getStackTrace();
                poolableConnection.connectStackTrace = stackTrace;
                poolableConnection.setConnectedTimeNano();
                poolableConnection.traceEnable = true;

                activeConnectionLock.lock();
                try {
                    activeConnections.put(poolableConnection, PRESENT);
                } finally {
                    activeConnectionLock.unlock();
                }
            }

            if (!this.defaultAutoCommit) {
                poolableConnection.setAutoCommit(false);
            }

            return poolableConnection;
        }
    }

    /**
     * 抛弃连接，不进行回收，而是抛弃
     * @param realConnection
     * @deprecated
     */
    public void discardConnection(Connection realConnection) {
        JdbcUtils.close(realConnection);

        lock.lock();
        try {
            activeCount--;
            discardCount++;

            if (activeCount <= minIdle) {
                emptySignal();
            }
        } finally {
            lock.unlock();
        }
    }

    public void discardConnection(DruidConnectionHolder holder) {
        if (holder == null) {
            return;
        }

        Connection conn = holder.getConnection();
        if (conn != null) {
            //关闭物理连接
            JdbcUtils.close(conn);
        }

        lock.lock();
        try {
            if (holder.discard) {
                return;
            }

            if (holder.active) {
                activeCount--;
                holder.active = false;
            }
            discardCount++;

            holder.discard = true;

            if (activeCount <= minIdle) {
                emptySignal();
            }
        } finally {
            lock.unlock();
        }
    }

    private DruidPooledConnection getConnectionInternal(long maxWait) throws SQLException {
        if (closed) {
            //已关闭
            connectErrorCountUpdater.incrementAndGet(this);
            throw new DataSourceClosedException("dataSource already closed at " + new Date(closeTimeMillis));
        }

        if (!enable) {
            //不可用
            connectErrorCountUpdater.incrementAndGet(this);

            if (disableException != null) {
                throw disableException;
            }

            throw new DataSourceDisableException();
        }

        final long nanos = TimeUnit.MILLISECONDS.toNanos(maxWait);
        final int maxWaitThreadCount = this.maxWaitThreadCount;

        DruidConnectionHolder holder;

        for (boolean createDirect = false; ; ) {
            if (createDirect) {
                //直接创建新的连接
                createStartNanosUpdater.set(this, System.nanoTime());
                if (creatingCountUpdater.compareAndSet(this, 0, 1)) {
                    PhysicalConnectionInfo pyConnInfo = DruidDataSource.this.createPhysicalConnection();
                    holder = new DruidConnectionHolder(this, pyConnInfo);
                    holder.lastActiveTimeMillis = System.currentTimeMillis();

                    creatingCountUpdater.decrementAndGet(this);
                    directCreateCountUpdater.incrementAndGet(this);

                    if (LOG.isDebugEnabled()) {
                        LOG.debug("conn-direct_create ");
                    }

                    boolean discard = false;
                    lock.lock();
                    try {
                        if (activeCount < maxActive) {
                            activeCount++;
                            holder.active = true;
                            if (activeCount > activePeak) {
                                activePeak = activeCount;
                                activePeakTime = System.currentTimeMillis();
                            }
                            break;
                        } else {
                            discard = true;
                        }
                    } finally {
                        lock.unlock();
                    }

                    if (discard) {
                        JdbcUtils.close(pyConnInfo.getPhysicalConnection());
                    }
                }
            }

            try {
                lock.lockInterruptibly();
            } catch (InterruptedException e) {
                connectErrorCountUpdater.incrementAndGet(this);
                throw new SQLException("interrupt", e);
            }

            try {
                if (maxWaitThreadCount > 0 && notEmptyWaitThreadCount >= maxWaitThreadCount) {
                    connectErrorCountUpdater.incrementAndGet(this);
                    throw new SQLException("maxWaitThreadCount " + maxWaitThreadCount + ", current wait Thread count " + lock
                            .getQueueLength());
                }

                if (onFatalError && onFatalErrorMaxActive > 0 && activeCount >= onFatalErrorMaxActive) {
                    connectErrorCountUpdater.incrementAndGet(this);

                    StringBuilder errorMsg = new StringBuilder();
                    errorMsg.append("onFatalError, activeCount ")
                            .append(activeCount)
                            .append(", onFatalErrorMaxActive ")
                            .append(onFatalErrorMaxActive);

                    if (lastFatalErrorTimeMillis > 0) {
                        errorMsg.append(", time '")
                                .append(StringUtils.formatDateTime19(lastFatalErrorTimeMillis, TimeZone.getDefault()))
                                .append("'");
                    }

                    if (lastFatalErrorSql != null) {
                        errorMsg.append(", sql \n").append(lastFatalErrorSql);
                    }

                    throw new SQLException(errorMsg.toString(), lastFatalError);
                }

                connectCount++;

                if (createScheduler != null && poolingCount == 0 && activeCount < maxActive && creatingCountUpdater
                        .get(this) == 0 && createScheduler instanceof ScheduledThreadPoolExecutor) {
                    //异步初始化
                    ScheduledThreadPoolExecutor executor = (ScheduledThreadPoolExecutor) createScheduler;
                    if (executor.getQueue().size() > 0) {
                        //直接创建新的连接
                        createDirect = true;
                        continue;
                    }
                }

                if (maxWait > 0) {
                    //有超时时间
                    holder = pollLast(nanos);
                } else {
                    //无超时时间
                    holder = takeLast();
                }

                if (holder != null) {
                    if (holder.discard) {
                        continue;
                    }

                    activeCount++;
                    //设置holder活跃状态
                    holder.active = true;
                    if (activeCount > activePeak) {
                        //更新活跃计数峰值
                        activePeak = activeCount;
                        activePeakTime = System.currentTimeMillis();
                    }
                }
            } catch (InterruptedException e) {
                connectErrorCountUpdater.incrementAndGet(this);
                throw new SQLException(e.getMessage(), e);
            } catch (SQLException e) {
                connectErrorCountUpdater.incrementAndGet(this);
                throw e;
            } finally {
                lock.unlock();
            }

            break;
        }

        if (holder == null) {
            long waitNanos = waitNanosLocal.get();

            StringBuilder buf = new StringBuilder(128);
            buf.append("wait millis ")//
                    .append(waitNanos / (1000 * 1000))//
                    .append(", active ").append(activeCount)//
                    .append(", maxActive ").append(maxActive)//
                    .append(", creating ").append(creatingCount)//
            ;
            if (creatingCount > 0 && createStartNanos > 0) {
                long createElapseMillis = (System.nanoTime() - createStartNanos) / (1000 * 1000);
                if (createElapseMillis > 0) {
                    buf.append(", createElapseMillis ").append(createElapseMillis);
                }
            }

            if (createErrorCount > 0) {
                buf.append(", createErrorCount ").append(createErrorCount);
            }

            List<JdbcSqlStatValue> sqlList = this.getDataSourceStat().getRuningSqlList();
            for (int i = 0; i < sqlList.size(); ++i) {
                if (i != 0) {
                    buf.append('\n');
                } else {
                    buf.append(", ");
                }
                JdbcSqlStatValue sql = sqlList.get(i);
                buf.append("runningSqlCount ").append(sql.getRunningCount());
                buf.append(" : ");
                buf.append(sql.getSql());
            }

            String errorMessage = buf.toString();

            if (this.createError != null) {
                throw new GetConnectionTimeoutException(errorMessage, createError);
            } else {
                throw new GetConnectionTimeoutException(errorMessage);
            }
        }

        holder.incrementUseCount();

        DruidPooledConnection poolalbeConnection = new DruidPooledConnection(holder);
        return poolalbeConnection;
    }

    public void handleConnectionException(DruidPooledConnection pooledConnection, Throwable t, String sql) throws SQLException {
        final DruidConnectionHolder holder = pooledConnection.getConnectionHolder();
        if (holder == null) {
            return;
        }

        errorCountUpdater.incrementAndGet(this);
        lastError = t;
        lastErrorTimeMillis = System.currentTimeMillis();

        if (t instanceof SQLException) {
            SQLException sqlEx = (SQLException) t;

            // broadcastConnectionError
            ConnectionEvent event = new ConnectionEvent(pooledConnection, sqlEx);
            for (ConnectionEventListener eventListener : holder.getConnectionEventListeners()) {
                eventListener.connectionErrorOccurred(event);
            }

            // exceptionSorter.isExceptionFatal
            if (exceptionSorter != null && exceptionSorter.isExceptionFatal(sqlEx)) {
                handleFatalError(pooledConnection, sqlEx, sql);
            }

            throw sqlEx;
        } else {
            throw new SQLException("Error", t);
        }
    }

    protected final void handleFatalError(DruidPooledConnection conn, SQLException error, String sql) throws SQLException {
        final DruidConnectionHolder holder = conn.holder;

        if (conn.isTraceEnable()) {
            activeConnectionLock.lock();
            try {
                if (conn.isTraceEnable()) {
                    activeConnections.remove(conn);
                    conn.setTraceEnable(false);
                }
            } finally {
                activeConnectionLock.unlock();
            }
        }

        long lastErrorTimeMillis = this.lastErrorTimeMillis;
        if (lastErrorTimeMillis == 0) {
            lastErrorTimeMillis = System.currentTimeMillis();
        }

        if (sql != null && sql.length() > 1024) {
            sql = sql.substring(0, 1024);
        }

        boolean requireDiscard = false;
        final ReentrantLock lock = conn.lock;
        lock.lock();
        try {
            if ((!conn.isClosed()) || !conn.isDisable()) {
                conn.disable(error);
                requireDiscard = true;
            }

            lastFatalErrorTimeMillis = lastErrorTimeMillis;
            fatalErrorCount++;
            if (fatalErrorCount - fatalErrorCountLastShrink > onFatalErrorMaxActive) {
                onFatalError = true;
            }
            lastFatalError = error;
            lastFatalErrorSql = sql;
        } finally {
            lock.unlock();
        }

        if (onFatalError && holder != null && holder.getDataSource() != null) {
            ReentrantLock dataSourceLock = holder.getDataSource().lock;
            dataSourceLock.lock();
            try {
                emptySignal();
            } finally {
                dataSourceLock.unlock();
            }
        }

        if (requireDiscard) {
            if (holder.statementTrace != null) {
                holder.lock.lock();
                try {
                    for (Statement stmt : holder.statementTrace) {
                        JdbcUtils.close(stmt);
                    }
                } finally {
                    holder.lock.unlock();
                }
            }

            this.discardConnection(holder);
        }

        LOG.error("discard connection", error);
    }

    /**
     * 回收连接
     */
    protected void recycle(DruidPooledConnection pooledConnection) throws SQLException {
        final DruidConnectionHolder holder = pooledConnection.holder;

        if (holder == null) {
            LOG.warn("connectionHolder is null");
            return;
        }

        if (logDifferentThread //
                && (!isAsyncCloseConnectionEnable()) //
                && pooledConnection.ownerThread != Thread.currentThread()//
        ) {
            LOG.warn("get/close not same thread");
        }

        //获取包装中的原始物理连接
        final Connection physicalConnection = holder.conn;

        if (pooledConnection.traceEnable) {
            Object oldInfo = null;
            activeConnectionLock.lock();
            try {
                if (pooledConnection.traceEnable) {
                    oldInfo = activeConnections.remove(pooledConnection);
                    pooledConnection.traceEnable = false;
                }
            } finally {
                activeConnectionLock.unlock();
            }
            if (oldInfo == null) {
                if (LOG.isWarnEnabled()) {
                    LOG.warn("remove abandonded failed. activeConnections.size " + activeConnections.size());
                }
            }
        }

        final boolean isAutoCommit = holder.underlyingAutoCommit;
        final boolean isReadOnly = holder.underlyingReadOnly;
        final boolean testOnReturn = this.testOnReturn;

        try {
            // check need to rollback?
            if ((!isAutoCommit) && (!isReadOnly)) {
                //是手动提交 并且 不是只读
                //回滚事务
                pooledConnection.rollback();
            }

            // reset holder, restore default settings, clear warnings
            boolean isSameThread = pooledConnection.ownerThread == Thread.currentThread();
            if (!isSameThread) {
                //和创建线程不是同一个线程
                final ReentrantLock lock = pooledConnection.lock;
                //加锁，这个锁和holder持有的锁是同一个锁对象
                lock.lock();
                try {
                    holder.reset();
                } finally {
                    lock.unlock();
                }
            } else {
                //和创建线程是同一个线程，不需要加锁
                holder.reset();
            }

            if (holder.discard) {
                //丢弃
                return;
            }

            if (phyMaxUseCount > 0 && holder.useCount >= phyMaxUseCount) {
                discardConnection(holder);
                return;
            }

            if (physicalConnection.isClosed()) {
                //如果物理连接已关闭
                lock.lock();
                try {
                    if (holder.active) {
                        //变更holder的活跃状态
                        activeCount--;
                        holder.active = false;
                    }
                    closeCount++;
                } finally {
                    lock.unlock();
                }
                return;
            }

            if (testOnReturn) {
                boolean validate = testConnectionInternal(holder, physicalConnection);
                if (!validate) {
                    JdbcUtils.close(physicalConnection);

                    destroyCountUpdater.incrementAndGet(this);

                    lock.lock();
                    try {
                        if (holder.active) {
                            activeCount--;
                            holder.active = false;
                        }
                        closeCount++;
                    } finally {
                        lock.unlock();
                    }
                    return;
                }
            }

            if (!enable) {
                //不可用
                //丢弃连接，关闭物理连接
                discardConnection(holder);
                return;
            }

            boolean result;
            final long currentTimeMillis = System.currentTimeMillis();

            if (phyTimeoutMillis > 0) {
                long phyConnectTimeMillis = currentTimeMillis - holder.connectTimeMillis;
                if (phyConnectTimeMillis > phyTimeoutMillis) {
                    discardConnection(holder);
                    return;
                }
            }

            //加锁
            lock.lock();
            try {
                if (holder.active) {
                    //活跃数量-1
                    activeCount--;
                    //变更holder活跃状态
                    holder.active = false;
                }

                //更新connection关闭计数，可以与回收计数作对比使用
                closeCount++;

                //回收到空闲连接池connections的末尾
                result = putLast(holder, currentTimeMillis);
                //更新回收计数
                recycleCount++;
            } finally {
                lock.unlock();
            }

            if (!result) {
                //putLast返回false，表示连接数已经超过配置的最大活跃数了，或者已经被丢弃，直接关闭。
                JdbcUtils.close(holder.conn);
                LOG.info("connection recyle failed.");
            }
        } catch (Throwable e) {
            //清空连接的PreparedStatementPool
            holder.clearStatementCache();

            if (!holder.discard) {
                //异常时，丢弃连接
                discardConnection(holder);
                holder.discard = true;
            }

            LOG.error("recyle error", e);
            //更新回收错误计数
            recycleErrorCountUpdater.incrementAndGet(this);
        }
    }

    public long getRecycleErrorCount() {
        return recycleErrorCount;
    }

    public void clearStatementCache() throws SQLException {
        lock.lock();
        try {
            for (int i = 0; i < poolingCount; ++i) {
                DruidConnectionHolder conn = connections[i];

                if (conn.statementPool != null) {
                    conn.statementPool.clear();
                }
            }
        } finally {
            lock.unlock();
        }
    }

    /**
     * close datasource
     */
    public void close() {
        //关闭连接池
        if (LOG.isInfoEnabled()) {
            LOG.info("{dataSource-" + this.getID() + "} closing ...");
        }

        lock.lock();
        try {
            if (this.closed) {
                //已关闭
                return;
            }

            if (!this.inited) {
                //未初始化或者为完成初始化
                return;
            }

            //关闭中 状态位
            this.closing = true;

            if (logStatsThread != null) {
                //中断日志线程
                logStatsThread.interrupt();
            }

            if (createConnectionThread != null) {
                //中断创建连接线程
                createConnectionThread.interrupt();
            }

            if (destroyConnectionThread != null) {
                //中断销毁连接线程
                destroyConnectionThread.interrupt();
            }

            if (createSchedulerFuture != null) {
                //取消连接创建任务
                createSchedulerFuture.cancel(true);
            }

            if (destroySchedulerFuture != null) {
                //TODO 取消连接销毁任务？？
                destroySchedulerFuture.cancel(true);
            }

            for (int i = 0; i < poolingCount; ++i) {
                //清理空闲连接池，加锁了，放心清理
                DruidConnectionHolder connHolder = connections[i];

                for (PreparedStatementHolder stmtHolder : connHolder.getStatementPool()
                        .getMap()
                        .values()) {
                    //关闭，删除连接缓存的statement
                    connHolder.getStatementPool().closeRemovedStatement(stmtHolder);
                }
                //清理statement池
                connHolder.getStatementPool().getMap().clear();

                Connection physicalConnection = connHolder.getConnection();
                try {
                    //关闭物理连接
                    physicalConnection.close();
                } catch (Exception ex) {
                    LOG.warn("close connection error", ex);
                }
                //从空闲连接池中删除
                connections[i] = null;
                //更新销毁计数
                destroyCountUpdater.incrementAndGet(this);
            }

            //清理完成，空闲连接池为空
            poolingCount = 0;
            //取消jmx注册的mbean
            unregisterMbean();

            //置为不可用
            enable = false;
            //唤醒所有消费者线程，让他们正常执行完毕
            notEmpty.signalAll();
            notEmptySignalCount++;

            //置为已关闭
            this.closed = true;
            this.closeTimeMillis = System.currentTimeMillis();

            //想保存关闭时的堆栈信息
            disableException = new DataSourceDisableException();

            for (Filter filter : filters) {
                //销毁过滤器
                filter.destroy();
            }
        } finally {
            lock.unlock();
        }

        if (LOG.isInfoEnabled()) {
            LOG.info("{dataSource-" + this.getID() + "} closed");
        }
    }

    public void registerMbean() {
        if (!mbeanRegistered) {
            AccessController.doPrivileged(new PrivilegedAction<Object>() {

                @Override
                public Object run() {
                    ObjectName objectName = DruidDataSourceStatManager.addDataSource(DruidDataSource.this, DruidDataSource.this.name);

                    DruidDataSource.this.setObjectName(objectName);
                    DruidDataSource.this.mbeanRegistered = true;

                    return null;
                }
            });
        }
    }

    public void unregisterMbean() {
        if (mbeanRegistered) {
            AccessController.doPrivileged(new PrivilegedAction<Object>() {

                @Override
                public Object run() {
                    DruidDataSourceStatManager.removeDataSource(DruidDataSource.this);
                    DruidDataSource.this.mbeanRegistered = false;
                    return null;
                }
            });
        }
    }

    public boolean isMbeanRegistered() {
        return mbeanRegistered;
    }

    boolean putLast(DruidConnectionHolder e, long lastActiveTimeMillis) {
        if (poolingCount >= maxActive || e.discard) {
            //如果空闲连接数量 >= 配置的最大活跃数 或者 hoder被丢弃
            //不做put操作，即不回收到空闲连接池，直接返回false
            return false;
        }

        //更新holder的最后活跃时间
        e.lastActiveTimeMillis = lastActiveTimeMillis;
        //将holder放到poolingCount位置
        connections[poolingCount] = e;
        //空闲连接计数+1
        incrementPoolingCount();

        if (poolingCount > poolingPeak) {
            //更新空闲连接池数量峰值
            poolingPeak = poolingCount;
            poolingPeakTime = lastActiveTimeMillis;
        }

        //唤醒一个消费者线程
        notEmpty.signal();
        //更新计数
        notEmptySignalCount++;

        return true;
    }

    DruidConnectionHolder takeLast() throws InterruptedException, SQLException {
        try {
            //空闲连接池为空 和有超时的pollLast(long nanos)逻辑类似
            while (poolingCount == 0) {
                //先唤醒生产线程，创建连接
                //现在没有空闲连接，如果没有运行中的生产线程，或者说不唤醒生产线程的话，那么这个方法一定获取不到连接，
                //或者说即使到了超时时间，也获取不到连接。因为没人生产连接。
                emptySignal(); // send signal to CreateThread create connection

                if (failFast && isFailContinuous()) {
                    //快速失败 和 连续失败
                    throw new DataSourceNotAvailableException(createError);
                }

                //等待中的消费者线程数量+1
                notEmptyWaitThreadCount++;
                if (notEmptyWaitThreadCount > notEmptyWaitThreadPeak) {
                    //peak 峰值的意思。
                    //如果等待数量大于记录的峰值，更新峰值。
                    notEmptyWaitThreadPeak = notEmptyWaitThreadCount;
                }
                try {
                    //消费者线程阻塞等待
                    notEmpty.await(); // signal by recycle or creator
                } finally {
                    //唤醒后等待计数-1
                    notEmptyWaitThreadCount--;
                }
                //消费者等待计数+1
                notEmptyWaitCount++;

                if (!enable) {
                    //不可用
                    connectErrorCountUpdater.incrementAndGet(this);
                    if (disableException != null) {
                        throw disableException;
                    }

                    throw new DataSourceDisableException();
                }
            }
        } catch (InterruptedException ie) {
            //当前消费者被中断了，此时要考虑锁被当前消费者持有，要唤醒另一个消费者线程
            notEmpty.signal(); // propagate to non-interrupted thread
            //消费者唤醒计数+1
            notEmptySignalCount++;
            //抛出异常，快速跳到外部cache或者finally代码块，里面会释放锁。这里应该是考虑了要快速释放锁。
            throw ie;
        }

        //空闲连接池connections非空 下面的逻辑和有超时pollLast(long nanos)里面的逻辑一样，取最后一个
        //空闲连接池计数poolingCount减一，减一后poolingCount就是最后一个连接的数组下标
        decrementPoolingCount();
        //取最后一个空闲连接
        DruidConnectionHolder last = connections[poolingCount];
        //将空闲连接池对应位置置为null
        connections[poolingCount] = null;

        //返回连接
        return last;
    }

    private DruidConnectionHolder pollLast(long nanos) throws InterruptedException, SQLException {
        //estimate 预估、估计的意思。表示距离超时还有多少纳秒。
        long estimate = nanos;

        for (; ; ) {
            //空闲连接池为空 和无超时的takeLast()逻辑类似
            if (poolingCount == 0) {
                //先唤醒生产线程，创建连接
                //现在没有空闲连接，如果没有运行中的生产线程，或者说不唤醒生产线程的话，那么这个方法一定获取不到连接，
                //或者说即使到了超时时间，也获取不到连接。因为没人生产连接。
                emptySignal(); // send signal to CreateThread create connection

                if (failFast && isFailContinuous()) {
                    //快速失败 和 连续失败
                    throw new DataSourceNotAvailableException(createError);
                }

                if (estimate <= 0) {
                    //等待超时了，设置当前线程实际等待了多久。ThreadLocal类型
                    waitNanosLocal.set(nanos - estimate);
                    //超时返回null
                    return null;
                }

                //处于等待中的消费者线程数量+1
                notEmptyWaitThreadCount++;
                if (notEmptyWaitThreadCount > notEmptyWaitThreadPeak) {
                    //peak 峰值的意思。
                    //如果等待数量大于记录的峰值，更新峰值。
                    notEmptyWaitThreadPeak = notEmptyWaitThreadCount;
                }

                try {
                    long startEstimate = estimate;

                    //消费者线程等待超时，此时之前唤醒的生产者线程正在创建连接，生产者线程创建完连接后会调用notEmpty.signal()，唤醒消费者线程，
                    //消费者线程被提前唤醒，或者阻塞超时后，都会更新estimate的值，这个值还是为距离超时还有多少纳秒。
                    //详见com.alibaba.druid.pool.DruidDataSource.put(com.alibaba.druid.pool.DruidConnectionHolder, long)
                    estimate = notEmpty.awaitNanos(estimate); // signal by
                    // recycle or
                    // creator
                    notEmptyWaitCount++;
                    notEmptyWaitNanos += (startEstimate - estimate);

                    if (!enable) {
                        //不可用
                        connectErrorCountUpdater.incrementAndGet(this);

                        if (disableException != null) {
                            throw disableException;
                        }

                        throw new DataSourceDisableException();
                    }
                } catch (InterruptedException ie) {
                    //当前消费者被中断了，此时要考虑锁被当前消费者持有，要唤醒另一个消费者线程
                    notEmpty.signal(); // propagate to non-interrupted thread
                    //消费者唤醒计数+1
                    notEmptySignalCount++;
                    //抛出异常，快速跳到外部cache或者finally代码块，里面会释放锁。这里应该是考虑了要快速释放锁。
                    throw ie;
                } finally {
                    //等待中的消费者线程数量-1s
                    notEmptyWaitThreadCount--;
                }

                //消费者线程被唤醒，或者达到超时时间醒来后。
                //判断如果此时空闲连接池还是为空，可能被别的消费者拿走了，或者创建失败等。
                if (poolingCount == 0) {
                    //空闲连接池为空
                    if (estimate > 0) {
                        //还没有达到超时时间，继续
                        continue;
                    }

                    //否则达到了超时时间
                    //更新等了多久了
                    waitNanosLocal.set(nanos - estimate);
                    //超时，返回null
                    return null;
                }
            }

            //空闲连接池connections非空 下面的逻辑和永不超时takeLast()里面的逻辑一样，取最后一个
            //空闲连接池计数poolingCount减一，减一后poolingCount就是最后一个连接的数组下标
            decrementPoolingCount();
            //取最后一个空闲连接
            DruidConnectionHolder last = connections[poolingCount];
            //将空闲连接池对应位置置为null
            connections[poolingCount] = null;

            //因为入参传了超时时间，这里计算下wait时间
            long waitNanos = nanos - estimate;
            //更新
            last.setLastNotEmptyWaitNanos(waitNanos);

            return last;
        }
    }

    private final void decrementPoolingCount() {
        poolingCount--;
    }

    private final void incrementPoolingCount() {
        poolingCount++;
    }

    @Override
    public Connection getConnection(String username, String password) throws SQLException {
        if (this.username == null && this.password == null && username != null && password != null) {
            this.username = username;
            this.password = password;

            return getConnection();
        }

        if (!StringUtils.equals(username, this.username)) {
            throw new UnsupportedOperationException("Not supported by DruidDataSource");
        }

        if (!StringUtils.equals(password, this.password)) {
            throw new UnsupportedOperationException("Not supported by DruidDataSource");
        }

        return getConnection();
    }

    public long getCreateCount() {
        return createCount;
    }

    public long getDestroyCount() {
        return destroyCount;
    }

    public long getConnectCount() {
        lock.lock();
        try {
            return connectCount;
        } finally {
            lock.unlock();
        }
    }

    public long getCloseCount() {
        return closeCount;
    }

    public long getConnectErrorCount() {
        return connectErrorCountUpdater.get(this);
    }

    @Override
    public int getPoolingCount() {
        lock.lock();
        try {
            return poolingCount;
        } finally {
            lock.unlock();
        }
    }

    public int getPoolingPeak() {
        lock.lock();
        try {
            return poolingPeak;
        } finally {
            lock.unlock();
        }
    }

    public Date getPoolingPeakTime() {
        if (poolingPeakTime <= 0) {
            return null;
        }

        return new Date(poolingPeakTime);
    }

    public long getRecycleCount() {
        return recycleCount;
    }

    public int getActiveCount() {
        lock.lock();
        try {
            return activeCount;
        } finally {
            lock.unlock();
        }
    }

    public void logStats() {
        final DruidDataSourceStatLogger statLogger = this.statLogger;
        if (statLogger == null) {
            return;
        }

        //收集封装线程池状态指标
        DruidDataSourceStatValue statValue = getStatValueAndReset();
        //转为map，使用json序列化，打印日志
        statLogger.log(statValue);
    }

    public DruidDataSourceStatValue getStatValueAndReset() {
        DruidDataSourceStatValue value = new DruidDataSourceStatValue();

        lock.lock();
        try {
            value.setPoolingCount(this.poolingCount);
            value.setPoolingPeak(this.poolingPeak);
            value.setPoolingPeakTime(this.poolingPeakTime);

            value.setActiveCount(this.activeCount);
            value.setActivePeak(this.activePeak);
            value.setActivePeakTime(this.activePeakTime);

            value.setConnectCount(this.connectCount);
            value.setCloseCount(this.closeCount);
            value.setWaitThreadCount(lock.getWaitQueueLength(notEmpty));
            value.setNotEmptyWaitCount(this.notEmptyWaitCount);
            value.setNotEmptyWaitNanos(this.notEmptyWaitNanos);
            value.setKeepAliveCheckCount(this.keepAliveCheckCount);

            // reset
            this.poolingPeak = 0;
            this.poolingPeakTime = 0;
            this.activePeak = 0;
            this.activePeakTime = 0;
            this.connectCount = 0;
            this.closeCount = 0;
            this.keepAliveCheckCount = 0;

            this.notEmptyWaitCount = 0;
            this.notEmptyWaitNanos = 0;
        } finally {
            lock.unlock();
        }

        value.setName(this.getName());
        value.setDbType(this.dbType);
        value.setDriverClassName(this.getDriverClassName());

        value.setUrl(this.getUrl());
        value.setUserName(this.getUsername());
        value.setFilterClassNames(this.getFilterClassNames());

        value.setInitialSize(this.getInitialSize());
        value.setMinIdle(this.getMinIdle());
        value.setMaxActive(this.getMaxActive());

        value.setQueryTimeout(this.getQueryTimeout());
        value.setTransactionQueryTimeout(this.getTransactionQueryTimeout());
        value.setLoginTimeout(this.getLoginTimeout());
        value.setValidConnectionCheckerClassName(this.getValidConnectionCheckerClassName());
        value.setExceptionSorterClassName(this.getExceptionSorterClassName());

        value.setTestOnBorrow(this.testOnBorrow);
        value.setTestOnReturn(this.testOnReturn);
        value.setTestWhileIdle(this.testWhileIdle);

        value.setDefaultAutoCommit(this.isDefaultAutoCommit());

        if (defaultReadOnly != null) {
            value.setDefaultReadOnly(defaultReadOnly);
        }
        value.setDefaultTransactionIsolation(this.getDefaultTransactionIsolation());

        value.setLogicConnectErrorCount(connectErrorCountUpdater.getAndSet(this, 0));

        value.setPhysicalConnectCount(createCountUpdater.getAndSet(this, 0));
        value.setPhysicalCloseCount(destroyCountUpdater.getAndSet(this, 0));
        value.setPhysicalConnectErrorCount(createErrorCountUpdater.getAndSet(this, 0));

        value.setExecuteCount(this.getAndResetExecuteCount());
        value.setErrorCount(errorCountUpdater.getAndSet(this, 0));
        value.setCommitCount(commitCountUpdater.getAndSet(this, 0));
        value.setRollbackCount(rollbackCountUpdater.getAndSet(this, 0));

        value.setPstmtCacheHitCount(cachedPreparedStatementHitCountUpdater.getAndSet(this, 0));
        value.setPstmtCacheMissCount(cachedPreparedStatementMissCountUpdater.getAndSet(this, 0));

        value.setStartTransactionCount(startTransactionCountUpdater.getAndSet(this, 0));
        value.setTransactionHistogram(this.getTransactionHistogram().toArrayAndReset());

        value.setConnectionHoldTimeHistogram(this.getDataSourceStat()
                .getConnectionHoldHistogram()
                .toArrayAndReset());
        value.setRemoveAbandoned(this.isRemoveAbandoned());
        value.setClobOpenCount(this.getDataSourceStat().getClobOpenCountAndReset());
        value.setBlobOpenCount(this.getDataSourceStat().getBlobOpenCountAndReset());

        value.setSqlSkipCount(this.getDataSourceStat().getSkipSqlCountAndReset());
        value.setSqlList(this.getDataSourceStat().getSqlStatMapAndReset());

        return value;
    }

    public long getRemoveAbandonedCount() {
        return removeAbandonedCount;
    }

    protected boolean put(PhysicalConnectionInfo physicalConnectionInfo) {
        DruidConnectionHolder holder = null;
        try {
            //将物理连接和创建它的连接池关联封装到一起
            holder = new DruidConnectionHolder(DruidDataSource.this, physicalConnectionInfo);
        } catch (SQLException ex) {
            lock.lock();
            //不是和DataSource初始化线程竞争锁，而是和连接销毁线程等竞争
            try {
                if (createScheduler != null) {
                    //是异步初始化，删除对应taskId的任务
                    clearCreateTask(physicalConnectionInfo.createTaskId);
                }
            } finally {
                lock.unlock();
            }
            LOG.error("create connection holder error", ex);
            return false;
        }

        return put(holder, physicalConnectionInfo.createTaskId);
    }

    private boolean put(DruidConnectionHolder holder, long createTaskId) {
        //要加锁
        lock.lock();
        try {
            //避免新建超了的判断
            if (poolingCount >= maxActive) {
                //空闲连接数量 >= 配置的最大活跃数
                if (createScheduler != null) {
                    //异步初始化，删除对应taskId的任务，避免建超了
                    clearCreateTask(createTaskId);
                }
                return false;
            }

            //放入空闲连接池，对应下标
            connections[poolingCount] = holder;
            incrementPoolingCount();

            //更新下标
            if (poolingCount > poolingPeak) {
                poolingPeak = poolingCount;
                poolingPeakTime = System.currentTimeMillis();
            }

            //只放了一个空闲连接，所以只唤醒一个消费者线程
            notEmpty.signal();
            notEmptySignalCount++;

            if (createScheduler != null) {
                //异步初始化
                //删除对应taskId的创建连接任务
                clearCreateTask(createTaskId);

                //空闲连接池数 + 创建连接任务数 < 等待连接的消费者线程数
                if (poolingCount + createTaskCount < notEmptyWaitThreadCount
                        //活跃数 + 空闲数 + 创建连接任务数 < 配置的最大活跃连接数
                        && activeCount + poolingCount + createTaskCount < maxActive) {
                    //唤醒生产者线程
                    emptySignal();
                }
            }
        } finally {
            lock.unlock();
        }
        return true;
    }

    public class CreateConnectionTask implements Runnable {

        private int errorCount = 0;
        private boolean initTask = false;
        private final long taskId;

        public CreateConnectionTask() {
            taskId = createTaskIdSeedUpdater.getAndIncrement(DruidDataSource.this);
        }

        public CreateConnectionTask(boolean initTask) {
            taskId = createTaskIdSeedUpdater.getAndIncrement(DruidDataSource.this);
            this.initTask = initTask;
        }

        @Override
        public void run() {
            runInternal();
        }

        private void runInternal() {
            for (; ; ) {

                // addLast
                lock.lock();
                try {
                    if (closed || closing) {
                        //已关闭或者关闭中，清空创建连接任务
                        clearCreateTask(taskId);
                        return;
                    }

                    //连接生产者需要阻塞等待
                    boolean emptyWait = true;

                    //有创建错误 并且 空闲连接池为空
                    if (createError != null && poolingCount == 0) {
                        //生产者不用等了
                        emptyWait = false;
                    }

                    if (emptyWait) {
                        // 必须存在线程等待，才创建连接
                        if (poolingCount >= notEmptyWaitThreadCount //
                                && (!(keepAlive && activeCount + poolingCount < minIdle)) // 在keepAlive场景不能放弃创建
                                && (!initTask) // 线程池初始化时的任务不能放弃创建
                                && !isFailContinuous() // failContinuous时不能放弃创建，否则会无法创建线程
                                && !isOnFatalError() // onFatalError时不能放弃创建，否则会无法创建线程
                        ) {
                            clearCreateTask(taskId);
                            return;
                        }

                        // 防止创建超过maxActive数量的连接
                        if (activeCount + poolingCount >= maxActive) {
                            clearCreateTask(taskId);
                            return;
                        }
                    }
                } finally {
                    lock.unlock();
                }

                PhysicalConnectionInfo physicalConnection = null;

                try {
                    physicalConnection = createPhysicalConnection();
                } catch (OutOfMemoryError e) {
                    LOG.error("create connection OutOfMemoryError, out memory. ", e);

                    errorCount++;
                    if (errorCount > connectionErrorRetryAttempts && timeBetweenConnectErrorMillis > 0) {
                        // fail over retry attempts
                        setFailContinuous(true);
                        if (failFast) {
                            lock.lock();
                            try {
                                notEmpty.signalAll();
                            } finally {
                                lock.unlock();
                            }
                        }

                        if (breakAfterAcquireFailure) {
                            lock.lock();
                            try {
                                clearCreateTask(taskId);
                            } finally {
                                lock.unlock();
                            }
                            return;
                        }

                        this.errorCount = 0; // reset errorCount
                        if (closing || closed) {
                            lock.lock();
                            try {
                                clearCreateTask(taskId);
                            } finally {
                                lock.unlock();
                            }
                            return;
                        }

                        createSchedulerFuture = createScheduler.schedule(this, timeBetweenConnectErrorMillis, TimeUnit.MILLISECONDS);
                        return;
                    }
                } catch (SQLException e) {
                    LOG.error("create connection SQLException, url: " + jdbcUrl, e);

                    errorCount++;
                    if (errorCount > connectionErrorRetryAttempts && timeBetweenConnectErrorMillis > 0) {
                        // fail over retry attempts
                        setFailContinuous(true);
                        if (failFast) {
                            lock.lock();
                            try {
                                notEmpty.signalAll();
                            } finally {
                                lock.unlock();
                            }
                        }

                        if (breakAfterAcquireFailure) {
                            lock.lock();
                            try {
                                clearCreateTask(taskId);
                            } finally {
                                lock.unlock();
                            }
                            return;
                        }

                        this.errorCount = 0; // reset errorCount
                        if (closing || closed) {
                            lock.lock();
                            try {
                                clearCreateTask(taskId);
                            } finally {
                                lock.unlock();
                            }
                            return;
                        }

                        createSchedulerFuture = createScheduler.schedule(this, timeBetweenConnectErrorMillis, TimeUnit.MILLISECONDS);
                        return;
                    }
                } catch (RuntimeException e) {
                    LOG.error("create connection RuntimeException", e);
                    // unknow fatal exception
                    setFailContinuous(true);
                    continue;
                } catch (Error e) {
                    lock.lock();
                    try {
                        clearCreateTask(taskId);
                    } finally {
                        lock.unlock();
                    }
                    LOG.error("create connection Error", e);
                    // unknow fatal exception
                    setFailContinuous(true);
                    break;
                } catch (Throwable e) {
                    lock.lock();
                    try {
                        clearCreateTask(taskId);
                    } finally {
                        lock.unlock();
                    }

                    LOG.error("create connection unexecpted error.", e);
                    break;
                }

                if (physicalConnection == null) {
                    continue;
                }

                physicalConnection.createTaskId = taskId;
                boolean result = put(physicalConnection);
                if (!result) {
                    JdbcUtils.close(physicalConnection.getPhysicalConnection());
                    LOG.info("put physical connection to pool failed.");
                }
                break;
            }
        }
    }

    public class CreateConnectionThread extends Thread {

        public CreateConnectionThread(String name) {
            super(name);
            //守护线程
            this.setDaemon(true);
        }

        public void run() {
            //initedLatch-1，执行DataSource初始化的主线程阻塞在CountDownLatch，在等待继续执行
            initedLatch.countDown();

            //最后丢弃的Connection数量
            long lastDiscardCount = 0;
            //错误数量
            int errorCount = 0;
            for (; ; ) {
                // addLast
                try {
                    //在DataSource初始化的时候，DataSource初始化线程持有lock锁
                    //保证该线程只有等连接池初始化完成，执行lock.unlock后，才可能持有锁，进行Connection创建，保证先后顺序关系。
                    //Connection销毁、put等方法执行时，也要持有lock锁，这些线程竞争，保证Connection创建和销毁的正确性。
                    lock.lockInterruptibly();
                } catch (InterruptedException e2) {
                    //线程中断，响应DataSource.close()方法
                    //退出循环，从for的范围看，也就是退出了run方法，线程执行完毕。
                    break;
                }

                //该连接池丢弃的Connection总数量
                long discardCount = DruidDataSource.this.discardCount;
                //在for循环的一次执行过程中，其他线程更新了总的discardCount，导致丢弃数量改变
                boolean discardChanged = discardCount - lastDiscardCount > 0;
                //更新lastDiscardCount，用于判断下一次循环时，总的discardCount是否发生了改变
                lastDiscardCount = discardCount;

                try {
                    //创建连接线程，是生产者-消费者模型中的生产者
                    //默认当前生产者线程阻塞等待，不创建新连接，感觉命名反了，这里应为fullWait
                    boolean emptyWait = true;

                    if (createError != null //整个DataSource创建Connection时出现过错误
                            && poolingCount == 0 //空闲连接池为空
                            && !discardChanged) { //没有出现新的丢弃连接事件
                        //生产者线程不用等了
                        emptyWait = false;
                    }

                    if (emptyWait //需要等待
                            && asyncInit //是异步初始化
                            && createCount < initialSize) { //已经创建完毕的连接数量 小于 配置的初始化数量
                        //生产者线程不用等了
                        emptyWait = false;
                    }

                    //生产者线程需要等待
                    if (emptyWait) {
                        // 必须存在线程等待，才创建连接
                        //考虑如果等待获取连接的消费者线程数量 >= 已生产的空闲连接数的话，就可能要立即生产新的连接，因为已经造成业务阻塞了。
                        if (poolingCount >= notEmptyWaitThreadCount //空闲连接数量 >= 等待获取连接的消费者线程数量
                                && (!(keepAlive && activeCount + poolingCount < minIdle))
                                //不保持存活，或者活跃连接数量+空闲连接数量 >= 配置的最小空闲连接数量
                                && !isFailContinuous() //不是连续失败
                        ) {
                            //生产者线程阻塞等待
                            empty.await();
                            //这里在虚假唤醒之后，可能出现的情况有
                            //1.在下一个if判断里，达到了最大活跃数限制，再次进入阻塞或者continue。这个逻辑没问题
                            //2.在下一个if判断里，没有达到最大活跃数限制，会走下面的创建连接的逻辑，
                            //因为没有达到最大活跃数限制，所以是可以创建新的连接的，只是新的连接可能不是被立即需要的，处于空闲状态。
                            //并且由于虚假唤醒的概率很低，这个发生的概率也很低。逻辑上也没有问题。
                        }

                        // 防止创建超过maxActive数量的连接
                        if (activeCount + poolingCount >= maxActive) {
                            //达到或者超过了配置的最大活跃连接数，生产者线程阻塞等待
                            empty.await();
                            //因为超了，唤醒后不会继续执行后面的创建连接逻辑，而是会重新走for循环，重新判断
                            //也要考虑虚假唤醒
                            continue;
                        }
                    }

                } catch (InterruptedException e) {
                    //保存最新的创建异常和时间
                    lastCreateError = e;
                    lastErrorTimeMillis = System.currentTimeMillis();

                    if (!closing) {
                        //如果不是关闭连接池造成的InterruptedException，记录日志
                        LOG.error("create connection Thread Interrupted, url: " + jdbcUrl, e);
                    }
                    break;
                } finally {
                    //生产者是否等待的判断逻辑走完，释放锁
                    lock.unlock();
                }


                //开始创建连接
                PhysicalConnectionInfo connection = null;

                try {
                    //创建连接
                    connection = createPhysicalConnection();
                } catch (SQLException e) {
                    LOG.error("create connection SQLException, url: " + jdbcUrl + ", errorCode " + e.getErrorCode() + ", state " + e
                            .getSQLState(), e);
                    //创建连接失败，或者执行验证sql失败等
                    errorCount++;
                    if (errorCount > connectionErrorRetryAttempts && timeBetweenConnectErrorMillis > 0) {
                        //错误数量 超过了 配置的错误重试次数
                        // fail over retry attempts
                        //设置为连续失败
                        setFailContinuous(true);
                        if (failFast) {
                            //快速失败
                            lock.lock();
                            try {
                                //激活所有消费者线程
                                notEmpty.signalAll();
                            } finally {
                                lock.unlock();
                            }
                        }

                        if (breakAfterAcquireFailure) {
                            //失败时退出for循环，退出线程
                            break;
                        }

                        try {
                            //睡眠，默认500毫秒
                            Thread.sleep(timeBetweenConnectErrorMillis);
                        } catch (InterruptedException interruptEx) {
                            //可能是关闭线程池操作导致的中断，退出循环，退出线程。但是这里应该像上面一样加个if (!closing)判断吧？？
                            break;
                        }
                    }
                } catch (RuntimeException e) {
                    LOG.error("create connection RuntimeException", e);
                    setFailContinuous(true);
                    continue;
                } catch (Error e) {
                    LOG.error("create connection Error", e);
                    setFailContinuous(true);
                    break;
                }

                if (connection == null) {
                    //重新走循环
                    continue;
                }

                //将新创建的连接放到空闲连接池connections中去
                boolean result = put(connection);
                if (!result) {
                    //放到空闲连接池失败，关闭物理连接，注意关闭的不是连接的包装对象，是关闭真实物理连接。这里和mybatis不一样。
                    JdbcUtils.close(connection.getPhysicalConnection());
                    LOG.info("put physical connection to pool failed.");
                }

                //重置下一次循环错误数为0
                errorCount = 0; // reset errorCount
            }
        }
    }

    public class DestroyConnectionThread extends Thread {

        public DestroyConnectionThread(String name) {
            super(name);
            //守护线程
            this.setDaemon(true);
        }

        public void run() {
            //initedLatch-1，执行DataSource初始化的主线程阻塞在CountDownLatch，在等待继续执行
            initedLatch.countDown();

            for (; ; ) {
                // 从前面开始删除
                try {
                    if (closed) {
                        //连接池已关闭
                        break;
                    }

                    if (timeBetweenEvictionRunsMillis > 0) {
                        Thread.sleep(timeBetweenEvictionRunsMillis);
                    } else {
                        Thread.sleep(1000); //
                    }

                    if (Thread.interrupted()) {
                        //响应线程池关闭动作
                        break;
                    }

                    destroyTask.run();
                } catch (InterruptedException e) {
                    break;
                }
            }
        }

    }

    public class DestroyTask implements Runnable {
        public DestroyTask() {

        }

        @Override
        public void run() {
            shrink(true, keepAlive);

            if (isRemoveAbandoned()) {
                removeAbandoned();
            }
        }

    }

    public class LogStatsThread extends Thread {

        public LogStatsThread(String name) {
            super(name);
            //守护线程
            this.setDaemon(true);
        }

        public void run() {
            try {
                for (; ; ) {
                    try {
                        logStats();
                    } catch (Exception e) {
                        LOG.error("logStats error", e);
                    }

                    Thread.sleep(timeBetweenLogStatsMillis);
                }
            } catch (InterruptedException e) {
                // skip
            }
        }
    }

    public int removeAbandoned() {
        int removeCount = 0;

        long currrentNanos = System.nanoTime();

        List<DruidPooledConnection> abandonedList = new ArrayList<DruidPooledConnection>();

        activeConnectionLock.lock();
        try {
            Iterator<DruidPooledConnection> iter = activeConnections.keySet().iterator();

            for (; iter.hasNext(); ) {
                DruidPooledConnection pooledConnection = iter.next();

                if (pooledConnection.isRunning()) {
                    continue;
                }

                long timeMillis = (currrentNanos - pooledConnection.getConnectedTimeNano()) / (1000 * 1000);

                if (timeMillis >= removeAbandonedTimeoutMillis) {
                    iter.remove();
                    pooledConnection.setTraceEnable(false);
                    abandonedList.add(pooledConnection);
                }
            }
        } finally {
            activeConnectionLock.unlock();
        }

        if (abandonedList.size() > 0) {
            for (DruidPooledConnection pooledConnection : abandonedList) {
                final ReentrantLock lock = pooledConnection.lock;
                lock.lock();
                try {
                    if (pooledConnection.isDisable()) {
                        continue;
                    }
                } finally {
                    lock.unlock();
                }

                JdbcUtils.close(pooledConnection);
                pooledConnection.abandond();
                removeAbandonedCount++;
                removeCount++;

                if (isLogAbandoned()) {
                    StringBuilder buf = new StringBuilder();
                    buf.append("abandon connection, owner thread: ");
                    buf.append(pooledConnection.getOwnerThread().getName());
                    buf.append(", connected at : ");
                    buf.append(pooledConnection.getConnectedTimeMillis());
                    buf.append(", open stackTrace\n");

                    StackTraceElement[] trace = pooledConnection.getConnectStackTrace();
                    for (int i = 0; i < trace.length; i++) {
                        buf.append("\tat ");
                        buf.append(trace[i].toString());
                        buf.append("\n");
                    }

                    buf.append("ownerThread current state is " + pooledConnection.getOwnerThread()
                            .getState() + ", current stackTrace\n");
                    trace = pooledConnection.getOwnerThread().getStackTrace();
                    for (int i = 0; i < trace.length; i++) {
                        buf.append("\tat ");
                        buf.append(trace[i].toString());
                        buf.append("\n");
                    }

                    LOG.error(buf.toString());
                }
            }
        }

        return removeCount;
    }

    /** Instance key */
    protected String instanceKey = null;

    public Reference getReference() throws NamingException {
        final String className = getClass().getName();
        final String factoryName = className + "Factory"; // XXX: not robust
        Reference ref = new Reference(className, factoryName, null);
        ref.add(new StringRefAddr("instanceKey", instanceKey));
        ref.add(new StringRefAddr("url", this.getUrl()));
        ref.add(new StringRefAddr("username", this.getUsername()));
        ref.add(new StringRefAddr("password", this.getPassword()));
        // TODO ADD OTHER PROPERTIES
        return ref;
    }

    @Override
    public List<String> getFilterClassNames() {
        List<String> names = new ArrayList<String>();
        for (Filter filter : filters) {
            names.add(filter.getClass().getName());
        }
        return names;
    }

    public int getRawDriverMajorVersion() {
        int version = -1;
        if (this.driver != null) {
            version = driver.getMajorVersion();
        }
        return version;
    }

    public int getRawDriverMinorVersion() {
        int version = -1;
        if (this.driver != null) {
            version = driver.getMinorVersion();
        }
        return version;
    }

    public String getProperties() {
        Properties properties = new Properties();
        properties.putAll(connectProperties);
        if (properties.containsKey("password")) {
            properties.put("password", "******");
        }
        return properties.toString();
    }

    @Override
    public void shrink() {
        shrink(false, false);
    }

    public void shrink(boolean checkTime) {
        shrink(checkTime, keepAlive);
    }

    //shrink 收缩的意思
    public void shrink(boolean checkTime, boolean keepAlive) {
        try {
            lock.lockInterruptibly();
        } catch (InterruptedException e) {
            return;
        }

        //是否需要生产连接，补充空闲连接池
        boolean needFill = false;
        //删除的数量
        int evictCount = 0;
        //保活数量
        int keepAliveCount = 0;
        //
        int fatalErrorIncrement = fatalErrorCount - fatalErrorCountLastShrink;
        fatalErrorCountLastShrink = fatalErrorCount;

        try {
            if (!inited) {
                return;
            }

            //配置的最小空闲连接数以外的连接数量
            final int checkCount = poolingCount - minIdle;
            final long currentTimeMillis = System.currentTimeMillis();
            for (int i = 0; i < poolingCount; ++i) {
                //遍历获取空闲连接池连接
                DruidConnectionHolder connection = connections[i];

                if ((onFatalError || fatalErrorIncrement > 0) //TODO 发生致命错误 或者 致命错误数有增长？？
                        && (lastFatalErrorTimeMillis > connection.connectTimeMillis)) {
                    //并且最后的致命错误发生在连接的连接动作之后
                    //放入保活连接池
                    keepAliveConnections[keepAliveCount++] = connection;
                    continue;
                }

                //入参指定需要做超时检查
                if (checkTime) {
                    //配置的物理连接超时时间
                    if (phyTimeoutMillis > 0) {
                        //物理连接操作持续时长 = for循环初次开始时间 - 连接操作开始时间
                        long phyConnectTimeMillis = currentTimeMillis - connection.connectTimeMillis;
                        if (phyConnectTimeMillis > phyTimeoutMillis) {
                            //实际持续时长超时了，放入待删除连接池中
                            evictConnections[evictCount++] = connection;
                            continue;
                        }
                    }

                    //空闲持续时长 = for循环初次开始时间 - 连接最后活跃时间
                    long idleMillis = currentTimeMillis - connection.lastActiveTimeMillis;

                    //如果连接的空闲时长 达到 可以被删除的最小空闲时长 就可以被回收删除了
                    // 如果达到了 可以被删除的最大空闲时长 是一定要被回收删除的
                    // 这里还加了一个保活操作 就是当属于minIdle数量以内的连接达到了 minEvictableIdleTimeMillis时，
                    // 优先考虑保活，不是考虑回收删除，这样维持连接池的数量达到minIdle的要求
                    // 所以一般配置的keepAliveBetweenTimeMillis值 是大于 minEvictableIdleTimeMillis的
                    // 这里的两个判断，后一个有点不理解，应该是防止人为配置错误，配置成keepAliveBetweenTimeMillis<minEvictableIdleTimeMillis
                    // 可能出现的时间顺序有：
                    //起点-->minEvictableIdleTimeMillis-->keepAliveBetweenTimeMillis-->maxEvictableIdleTimeMillis
                    //起点-->keepAliveBetweenTimeMillis-->minEvictableIdleTimeMillis-->maxEvictableIdleTimeMillis
                    //实际空闲时长 没有达到 可以被删除的最小空闲时长 && 也没有达到可以保活的空闲时长
                    if (idleMillis < minEvictableIdleTimeMillis && idleMillis < keepAliveBetweenTimeMillis) {
                        //退出遍历空闲连接池connections，不继续循环了，为什么呢？
                        //因为对于空闲连接池的操作一共可以分为两种，一个放连接，一个取连接
                        //放连接是从头开始放，取连接是从尾开始取，
                        // 这样的话越是在数组前面的连接一定越是空闲时间更长的，从前往后遍历，如果最前面的都没有达到删除和保活的要求，
                        //  那后面的一定也没有达到，这样就不需要再继续判断了，退出遍历即可。
                        break;
                    }

                    //实际空闲时长 已经达到 可以被删除的最小空闲时长
                    if (idleMillis >= minEvictableIdleTimeMillis) {
                        if (checkTime && i < checkCount) {
                            //需要超时检查 并且 属于最小空闲连接数以外的连接
                            //放入待删除连接池，相当于从头开始删除
                            evictConnections[evictCount++] = connection;
                            continue;
                        } else if (idleMillis > maxEvictableIdleTimeMillis) {
                            //当前连接下标 属于最小空闲连接数以内的连接
                            //但是实际空闲时长 超过了 可以被删除的最大空闲时长，这种一定要被删除，放入待删除连接池
                            evictConnections[evictCount++] = connection;
                            continue;
                        }
                    }

                    //走到这有的几种情况：
                    // 1. idleMillis >= minEvictableIdleTimeMillis 并且 当前连接下标 属于最小空闲连接数以内的连接 但是没有达到 可以被删除的最大空闲时长
                    // 2. idleMillis < minEvictableIdleTimeMillis 但是 idleMillis >= keepAliveBetweenTimeMillis
                    //入参指定要保活 并且 空闲时长 达到了 保活的空闲时长要求
                    //证明不指定保活的话，这些连接也就真的被删除了
                    if (keepAlive && idleMillis >= keepAliveBetweenTimeMillis) {
                        //放入保活连接池
                        keepAliveConnections[keepAliveCount++] = connection;
                    }
                } else {
                    //入参指定不需要做超时检查
                    if (i < checkCount) {
                        //当前连接下标属于最小空闲连接数以外的连接  放入待删除连接池
                        evictConnections[evictCount++] = connection;
                    } else {
                        //剩下的都属于最小空闲连接数以内的连接，不需要再判读删除了，退出循环
                        break;
                    }
                }
            }

            //删除数量 = 待删除数量 + 保活数量
            //对空闲连接池来说，要删除的数量就是这些，至于保活，删完了，后面有保活操作的话，会把保活连接再放回来
            int removeCount = evictCount + keepAliveCount;
            if (removeCount > 0) {
                //把空闲连接池分为两部分，0到removeCount-1，是空闲时间较长的，
                //removeCount到poolingCount是符合minIdle数量要求的，删除前面的连接，然后移动后面的连接，可以直接使用数组拷贝，
                //拷贝后面的连接 覆盖 前面的连接 然后 重置数组后面的位置为null
                System.arraycopy(connections, removeCount, connections, 0, poolingCount - removeCount);
                //对空闲连接池，用null填充后面的位置
                Arrays.fill(connections, poolingCount - removeCount, poolingCount, null);
                //更新空闲连接池计数
                poolingCount -= removeCount;
            }
            //更新总保活计数
            keepAliveCheckCount += keepAliveCount;

            //保活 并且 空闲连接数量 + 活跃数量 < 配置的最小连接数量
            if (keepAlive && poolingCount + activeCount < minIdle) {
                //连接不足 需要生产连接 补充连接池
                //如果没配置保活的话，配置的minIdle数量以内的连接，
                // 满足一定的条件时(主要为checkTime==true && idleMillis > maxEvictableIdleTimeMillis)，也是会被删除的。
                // 空闲连接池可能被删到空了，所以想保证有minIdle个空闲连接的话，keepAlive一定要配置为true
                needFill = true;
            }
        } finally {
            //释放锁
            lock.unlock();
        }

        //如果待删除连接池的长度 > 0
        if (evictCount > 0) {
            //遍历关闭连接
            for (int i = 0; i < evictCount; ++i) {
                DruidConnectionHolder item = evictConnections[i];
                Connection connection = item.getConnection();
                //关闭物理连接
                JdbcUtils.close(connection);
                destroyCountUpdater.incrementAndGet(this);
            }
            //删完，重置整个待删除连接池数组
            Arrays.fill(evictConnections, null);
        }

        //如果要保活的数量>0
        if (keepAliveCount > 0) {
            // keep order
            //保活连接池是从前往后遍历放的，因为后面的一定空闲时间更短，所以从后往前遍历保活
            for (int i = keepAliveCount - 1; i >= 0; --i) {
                DruidConnectionHolder holer = keepAliveConnections[i];
                Connection connection = holer.getConnection();
                holer.incrementKeepAliveCheckCount();

                boolean validate = false;
                try {
                    //验证连接是否有效，没抛异常就是有效
                    this.validateConnection(connection);
                    validate = true;
                } catch (Throwable error) {
                    if (LOG.isDebugEnabled()) {
                        LOG.debug("keepAliveErr", error);
                    }
                    // skip
                }

                //是否丢弃这个连接
                boolean discard = !validate;
                if (validate) {
                    //连接有效
                    holer.lastKeepTimeMillis = System.currentTimeMillis();
                    //保活 再放回到空闲连接池里去 放到最后面
                    boolean putOk = put(holer, 0L);
                    if (!putOk) {
                        //放不回去 就不保活了 丢弃
                        discard = true;
                    }
                }

                if (discard) {
                    //丢弃
                    try {
                        connection.close();
                    } catch (Exception e) {
                        // skip
                    }

                    lock.lock();
                    try {
                        //更新丢弃计数
                        discardCount++;

                        //如果活跃数+空闲数 <= 配置的最小空闲数
                        if (activeCount + poolingCount <= minIdle) {
                            //关了一个，再唤醒一个生产者线程
                            emptySignal();
                        }
                    } finally {
                        lock.unlock();
                    }
                }
            }
            //统计计数更新总的保活计数
            this.getDataSourceStat().addKeepAliveCheckCount(keepAliveCount);
            //清空保活连接池
            Arrays.fill(keepAliveConnections, null);
        }

        //连接不足 需要生产连接
        //needFill默认为false，开启保活的话，会根据情况更新为true
        if (needFill) {
            lock.lock();
            try {
                //需要补充的数量 最后连接总数量要达到配置的最小空闲连接数
                int fillCount = minIdle - (activeCount + poolingCount + createTaskCount);
                for (int i = 0; i < fillCount; ++i) {
                    //唤醒一个生产者线程
                    emptySignal();
                }
            } finally {
                lock.unlock();
            }
        } else if (onFatalError || fatalErrorIncrement > 0) {
            lock.lock();
            try {
                //唤醒有问题，再唤醒一个等待中的其他生产者
                emptySignal();
            } finally {
                lock.unlock();
            }
        }
    }

    public int getWaitThreadCount() {
        lock.lock();
        try {
            return lock.getWaitQueueLength(notEmpty);
        } finally {
            lock.unlock();
        }
    }

    public long getNotEmptyWaitCount() {
        return notEmptyWaitCount;
    }

    public int getNotEmptyWaitThreadCount() {
        lock.lock();
        try {
            return notEmptyWaitThreadCount;
        } finally {
            lock.unlock();
        }
    }

    public int getNotEmptyWaitThreadPeak() {
        lock.lock();
        try {
            return notEmptyWaitThreadPeak;
        } finally {
            lock.unlock();
        }
    }

    public long getNotEmptySignalCount() {
        return notEmptySignalCount;
    }

    public long getNotEmptyWaitMillis() {
        return notEmptyWaitNanos / (1000 * 1000);
    }

    public long getNotEmptyWaitNanos() {
        return notEmptyWaitNanos;
    }

    public int getLockQueueLength() {
        return lock.getQueueLength();
    }

    public int getActivePeak() {
        return activePeak;
    }

    public Date getActivePeakTime() {
        if (activePeakTime <= 0) {
            return null;
        }

        return new Date(activePeakTime);
    }

    public String dump() {
        lock.lock();
        try {
            return this.toString();
        } finally {
            lock.unlock();
        }
    }

    public long getErrorCount() {
        return this.errorCount;
    }

    public String toString() {
        StringBuilder buf = new StringBuilder();

        buf.append("{");

        buf.append("\n\tCreateTime:\"");
        buf.append(Utils.toString(getCreatedTime()));
        buf.append("\"");

        buf.append(",\n\tActiveCount:");
        buf.append(getActiveCount());

        buf.append(",\n\tPoolingCount:");
        buf.append(getPoolingCount());

        buf.append(",\n\tCreateCount:");
        buf.append(getCreateCount());

        buf.append(",\n\tDestroyCount:");
        buf.append(getDestroyCount());

        buf.append(",\n\tCloseCount:");
        buf.append(getCloseCount());

        buf.append(",\n\tConnectCount:");
        buf.append(getConnectCount());

        buf.append(",\n\tConnections:[");
        for (int i = 0; i < poolingCount; ++i) {
            DruidConnectionHolder conn = connections[i];
            if (conn != null) {
                if (i != 0) {
                    buf.append(",");
                }
                buf.append("\n\t\t");
                buf.append(conn.toString());
            }
        }
        buf.append("\n\t]");

        buf.append("\n}");

        if (this.isPoolPreparedStatements()) {
            buf.append("\n\n[");
            for (int i = 0; i < poolingCount; ++i) {
                DruidConnectionHolder conn = connections[i];
                if (conn != null) {
                    if (i != 0) {
                        buf.append(",");
                    }
                    buf.append("\n\t{\n\tID:");
                    buf.append(System.identityHashCode(conn.getConnection()));
                    PreparedStatementPool pool = conn.getStatementPool();

                    buf.append(", \n\tpoolStatements:[");

                    int entryIndex = 0;
                    try {
                        for (Map.Entry<PreparedStatementKey, PreparedStatementHolder> entry : pool.getMap()
                                .entrySet()) {
                            if (entryIndex != 0) {
                                buf.append(",");
                            }
                            buf.append("\n\t\t{hitCount:");
                            buf.append(entry.getValue().getHitCount());
                            buf.append(",sql:\"");
                            buf.append(entry.getKey().getSql());
                            buf.append("\"");
                            buf.append("\t}");

                            entryIndex++;
                        }
                    } catch (ConcurrentModificationException e) {
                        // skip ..
                    }

                    buf.append("\n\t\t]");

                    buf.append("\n\t}");
                }
            }
            buf.append("\n]");
        }

        return buf.toString();
    }

    public List<Map<String, Object>> getPoolingConnectionInfo() {
        List<Map<String, Object>> list = new ArrayList<Map<String, Object>>();
        lock.lock();
        try {
            for (int i = 0; i < poolingCount; ++i) {
                DruidConnectionHolder connHolder = connections[i];
                Connection conn = connHolder.getConnection();

                Map<String, Object> map = new LinkedHashMap<String, Object>();
                map.put("id", System.identityHashCode(conn));
                map.put("connectionId", connHolder.getConnectionId());
                map.put("useCount", connHolder.getUseCount());
                if (connHolder.lastActiveTimeMillis > 0) {
                    map.put("lastActiveTime", new Date(connHolder.lastActiveTimeMillis));
                }
                if (connHolder.lastKeepTimeMillis > 0) {
                    map.put("lastKeepTimeMillis", new Date(connHolder.lastKeepTimeMillis));
                }
                map.put("connectTime", new Date(connHolder.getTimeMillis()));
                map.put("holdability", connHolder.getUnderlyingHoldability());
                map.put("transactionIsolation", connHolder.getUnderlyingTransactionIsolation());
                map.put("autoCommit", connHolder.underlyingAutoCommit);
                map.put("readoOnly", connHolder.isUnderlyingReadOnly());

                if (connHolder.isPoolPreparedStatements()) {
                    List<Map<String, Object>> stmtCache = new ArrayList<Map<String, Object>>();
                    PreparedStatementPool stmtPool = connHolder.getStatementPool();
                    for (PreparedStatementHolder stmtHolder : stmtPool.getMap().values()) {
                        Map<String, Object> stmtInfo = new LinkedHashMap<String, Object>();

                        stmtInfo.put("sql", stmtHolder.key.getSql());
                        stmtInfo.put("defaultRowPrefetch", stmtHolder.getDefaultRowPrefetch());
                        stmtInfo.put("rowPrefetch", stmtHolder.getRowPrefetch());
                        stmtInfo.put("hitCount", stmtHolder.getHitCount());

                        stmtCache.add(stmtInfo);
                    }

                    map.put("pscache", stmtCache);
                }
                map.put("keepAliveCheckCount", connHolder.getKeepAliveCheckCount());

                list.add(map);
            }
        } finally {
            lock.unlock();
        }
        return list;
    }

    public void logTransaction(TransactionInfo info) {
        long transactionMillis = info.getEndTimeMillis() - info.getStartTimeMillis();
        if (transactionThresholdMillis > 0 && transactionMillis > transactionThresholdMillis) {
            StringBuilder buf = new StringBuilder();
            buf.append("long time transaction, take ");
            buf.append(transactionMillis);
            buf.append(" ms : ");
            for (String sql : info.getSqlList()) {
                buf.append(sql);
                buf.append(";");
            }
            LOG.error(buf.toString(), new TransactionTimeoutException());
        }
    }

    @Override
    public String getVersion() {
        return VERSION.getVersionNumber();
    }

    @Override
    public JdbcDataSourceStat getDataSourceStat() {
        return dataSourceStat;
    }

    public Object clone() throws CloneNotSupportedException {
        return cloneDruidDataSource();
    }

    public DruidDataSource cloneDruidDataSource() {
        DruidDataSource x = new DruidDataSource();

        cloneTo(x);

        return x;
    }

    public Map<String, Object> getStatDataForMBean() {
        try {
            Map<String, Object> map = new HashMap<String, Object>();

            // 0 - 4
            map.put("Name", this.getName());
            map.put("URL", this.getUrl());
            map.put("CreateCount", this.getCreateCount());
            map.put("DestroyCount", this.getDestroyCount());
            map.put("ConnectCount", this.getConnectCount());

            // 5 - 9
            map.put("CloseCount", this.getCloseCount());
            map.put("ActiveCount", this.getActiveCount());
            map.put("PoolingCount", this.getPoolingCount());
            map.put("LockQueueLength", this.getLockQueueLength());
            map.put("WaitThreadCount", this.getNotEmptyWaitThreadCount());

            // 10 - 14
            map.put("InitialSize", this.getInitialSize());
            map.put("MaxActive", this.getMaxActive());
            map.put("MinIdle", this.getMinIdle());
            map.put("PoolPreparedStatements", this.isPoolPreparedStatements());
            map.put("TestOnBorrow", this.isTestOnBorrow());

            // 15 - 19
            map.put("TestOnReturn", this.isTestOnReturn());
            map.put("MinEvictableIdleTimeMillis", this.minEvictableIdleTimeMillis);
            map.put("ConnectErrorCount", this.getConnectErrorCount());
            map.put("CreateTimespanMillis", this.getCreateTimespanMillis());
            map.put("DbType", this.dbType);

            // 20 - 24
            map.put("ValidationQuery", this.getValidationQuery());
            map.put("ValidationQueryTimeout", this.getValidationQueryTimeout());
            map.put("DriverClassName", this.getDriverClassName());
            map.put("Username", this.getUsername());
            map.put("RemoveAbandonedCount", this.getRemoveAbandonedCount());

            // 25 - 29
            map.put("NotEmptyWaitCount", this.getNotEmptyWaitCount());
            map.put("NotEmptyWaitNanos", this.getNotEmptyWaitNanos());
            map.put("ErrorCount", this.getErrorCount());
            map.put("ReusePreparedStatementCount", this.getCachedPreparedStatementHitCount());
            map.put("StartTransactionCount", this.getStartTransactionCount());

            // 30 - 34
            map.put("CommitCount", this.getCommitCount());
            map.put("RollbackCount", this.getRollbackCount());
            map.put("LastError", JMXUtils.getErrorCompositeData(this.getLastError()));
            map.put("LastCreateError", JMXUtils.getErrorCompositeData(this.getLastCreateError()));
            map.put("PreparedStatementCacheDeleteCount", this.getCachedPreparedStatementDeleteCount());

            // 35 - 39
            map.put("PreparedStatementCacheAccessCount", this.getCachedPreparedStatementAccessCount());
            map.put("PreparedStatementCacheMissCount", this.getCachedPreparedStatementMissCount());
            map.put("PreparedStatementCacheHitCount", this.getCachedPreparedStatementHitCount());
            map.put("PreparedStatementCacheCurrentCount", this.getCachedPreparedStatementCount());
            map.put("Version", this.getVersion());

            // 40 -
            map.put("LastErrorTime", this.getLastErrorTime());
            map.put("LastCreateErrorTime", this.getLastCreateErrorTime());
            map.put("CreateErrorCount", this.getCreateErrorCount());
            map.put("DiscardCount", this.getDiscardCount());
            map.put("ExecuteQueryCount", this.getExecuteQueryCount());

            map.put("ExecuteUpdateCount", this.getExecuteUpdateCount());

            return map;
        } catch (JMException ex) {
            throw new IllegalStateException("getStatData error", ex);
        }
    }

    public Map<String, Object> getStatData() {
        final int activeCount;
        final int activePeak;
        final Date activePeakTime;

        final int poolingCount;
        final int poolingPeak;
        final Date poolingPeakTime;

        final long connectCount;
        final long closeCount;

        lock.lock();
        try {
            poolingCount = this.poolingCount;
            poolingPeak = this.poolingPeak;
            poolingPeakTime = this.getPoolingPeakTime();

            activeCount = this.activeCount;
            activePeak = this.activePeak;
            activePeakTime = this.getActivePeakTime();

            connectCount = this.connectCount;
            closeCount = this.closeCount;
        } finally {
            lock.unlock();
        }
        Map<String, Object> dataMap = new LinkedHashMap<String, Object>();

        dataMap.put("Identity", System.identityHashCode(this));
        dataMap.put("Name", this.getName());
        dataMap.put("DbType", this.dbType);
        dataMap.put("DriverClassName", this.getDriverClassName());

        dataMap.put("URL", this.getUrl());
        dataMap.put("UserName", this.getUsername());
        dataMap.put("FilterClassNames", this.getFilterClassNames());

        dataMap.put("WaitThreadCount", this.getWaitThreadCount());
        dataMap.put("NotEmptyWaitCount", this.getNotEmptyWaitCount());
        dataMap.put("NotEmptyWaitMillis", this.getNotEmptyWaitMillis());

        dataMap.put("PoolingCount", poolingCount);
        dataMap.put("PoolingPeak", poolingPeak);
        dataMap.put("PoolingPeakTime", poolingPeakTime);

        dataMap.put("ActiveCount", activeCount);
        dataMap.put("ActivePeak", activePeak);
        dataMap.put("ActivePeakTime", activePeakTime);

        dataMap.put("InitialSize", this.getInitialSize());
        dataMap.put("MinIdle", this.getMinIdle());
        dataMap.put("MaxActive", this.getMaxActive());

        dataMap.put("QueryTimeout", this.getQueryTimeout());
        dataMap.put("TransactionQueryTimeout", this.getTransactionQueryTimeout());
        dataMap.put("LoginTimeout", this.getLoginTimeout());
        dataMap.put("ValidConnectionCheckerClassName", this.getValidConnectionCheckerClassName());
        dataMap.put("ExceptionSorterClassName", this.getExceptionSorterClassName());

        dataMap.put("TestOnBorrow", this.isTestOnBorrow());
        dataMap.put("TestOnReturn", this.isTestOnReturn());
        dataMap.put("TestWhileIdle", this.isTestWhileIdle());

        dataMap.put("DefaultAutoCommit", this.isDefaultAutoCommit());
        dataMap.put("DefaultReadOnly", this.getDefaultReadOnly());
        dataMap.put("DefaultTransactionIsolation", this.getDefaultTransactionIsolation());

        dataMap.put("LogicConnectCount", connectCount);
        dataMap.put("LogicCloseCount", closeCount);
        dataMap.put("LogicConnectErrorCount", this.getConnectErrorCount());

        dataMap.put("PhysicalConnectCount", this.getCreateCount());
        dataMap.put("PhysicalCloseCount", this.getDestroyCount());
        dataMap.put("PhysicalConnectErrorCount", this.getCreateErrorCount());

        dataMap.put("DiscardCount", this.getDiscardCount());

        dataMap.put("ExecuteCount", this.getExecuteCount());
        dataMap.put("ExecuteUpdateCount", this.getExecuteUpdateCount());
        dataMap.put("ExecuteQueryCount", this.getExecuteQueryCount());
        dataMap.put("ExecuteBatchCount", this.getExecuteBatchCount());
        dataMap.put("ErrorCount", this.getErrorCount());
        dataMap.put("CommitCount", this.getCommitCount());
        dataMap.put("RollbackCount", this.getRollbackCount());

        dataMap.put("PSCacheAccessCount", this.getCachedPreparedStatementAccessCount());
        dataMap.put("PSCacheHitCount", this.getCachedPreparedStatementHitCount());
        dataMap.put("PSCacheMissCount", this.getCachedPreparedStatementMissCount());

        dataMap.put("StartTransactionCount", this.getStartTransactionCount());
        dataMap.put("TransactionHistogram", this.getTransactionHistogramValues());

        dataMap.put("ConnectionHoldTimeHistogram", this.getDataSourceStat()
                .getConnectionHoldHistogram()
                .toArray());
        dataMap.put("RemoveAbandoned", this.isRemoveAbandoned());
        dataMap.put("ClobOpenCount", this.getDataSourceStat().getClobOpenCount());
        dataMap.put("BlobOpenCount", this.getDataSourceStat().getBlobOpenCount());
        dataMap.put("KeepAliveCheckCount", this.getDataSourceStat().getKeepAliveCheckCount());

        dataMap.put("KeepAlive", this.isKeepAlive());
        dataMap.put("FailFast", this.isFailFast());
        dataMap.put("MaxWait", this.getMaxWait());
        dataMap.put("MaxWaitThreadCount", this.getMaxWaitThreadCount());
        dataMap.put("PoolPreparedStatements", this.isPoolPreparedStatements());
        dataMap.put("MaxPoolPreparedStatementPerConnectionSize", this.getMaxPoolPreparedStatementPerConnectionSize());
        dataMap.put("MinEvictableIdleTimeMillis", this.minEvictableIdleTimeMillis);
        dataMap.put("MaxEvictableIdleTimeMillis", this.maxEvictableIdleTimeMillis);

        dataMap.put("LogDifferentThread", isLogDifferentThread());
        dataMap.put("RecycleErrorCount", getRecycleErrorCount());
        dataMap.put("PreparedStatementOpenCount", getPreparedStatementCount());
        dataMap.put("PreparedStatementClosedCount", getClosedPreparedStatementCount());

        dataMap.put("UseUnfairLock", isUseUnfairLock());
        dataMap.put("InitGlobalVariants", isInitGlobalVariants());
        dataMap.put("InitVariants", isInitVariants());
        return dataMap;
    }

    public JdbcSqlStat getSqlStat(int sqlId) {
        return this.getDataSourceStat().getSqlStat(sqlId);
    }

    public JdbcSqlStat getSqlStat(long sqlId) {
        return this.getDataSourceStat().getSqlStat(sqlId);
    }

    public Map<String, JdbcSqlStat> getSqlStatMap() {
        return this.getDataSourceStat().getSqlStatMap();
    }

    public Map<String, Object> getWallStatMap() {
        WallProviderStatValue wallStatValue = getWallStatValue(false);

        if (wallStatValue != null) {
            return wallStatValue.toMap();
        }

        return null;
    }

    public WallProviderStatValue getWallStatValue(boolean reset) {
        for (Filter filter : this.filters) {
            if (filter instanceof WallFilter) {
                WallFilter wallFilter = (WallFilter) filter;
                return wallFilter.getProvider().getStatValue(reset);
            }
        }

        return null;
    }

    public Lock getLock() {
        return lock;
    }

    @Override
    public boolean isWrapperFor(Class<?> iface) {
        for (Filter filter : this.filters) {
            if (filter.isWrapperFor(iface)) {
                return true;
            }
        }

        if (this.statLogger != null && (this.statLogger.getClass() == iface || DruidDataSourceStatLogger.class == iface)) {
            return true;
        }

        return super.isWrapperFor(iface);
    }

    @SuppressWarnings("unchecked")
    public <T> T unwrap(Class<T> iface) {
        for (Filter filter : this.filters) {
            if (filter.isWrapperFor(iface)) {
                return (T) filter;
            }
        }

        if (this.statLogger != null && (this.statLogger.getClass() == iface || DruidDataSourceStatLogger.class == iface)) {
            return (T) statLogger;
        }

        return super.unwrap(iface);
    }

    public boolean isLogDifferentThread() {
        return logDifferentThread;
    }

    public void setLogDifferentThread(boolean logDifferentThread) {
        this.logDifferentThread = logDifferentThread;
    }

    public DruidPooledConnection tryGetConnection() throws SQLException {
        if (poolingCount == 0) {
            return null;
        }
        return getConnection();
    }

    @Override
    public int fill() throws SQLException {
        return this.fill(this.maxActive);
    }

    @Override
    public int fill(int toCount) throws SQLException {
        if (closed) {
            throw new DataSourceClosedException("dataSource already closed at " + new Date(closeTimeMillis));
        }

        if (toCount < 0) {
            throw new IllegalArgumentException("toCount can't not be less than zero");
        }

        init();

        if (toCount > this.maxActive) {
            toCount = this.maxActive;
        }

        int fillCount = 0;
        for (; ; ) {
            try {
                lock.lockInterruptibly();
            } catch (InterruptedException e) {
                connectErrorCountUpdater.incrementAndGet(this);
                throw new SQLException("interrupt", e);
            }

            boolean fillable = this.isFillable(toCount);

            lock.unlock();

            if (!fillable) {
                break;
            }

            DruidConnectionHolder holder;
            try {
                PhysicalConnectionInfo pyConnInfo = createPhysicalConnection();
                holder = new DruidConnectionHolder(this, pyConnInfo);
            } catch (SQLException e) {
                LOG.error("fill connection error, url: " + this.jdbcUrl, e);
                connectErrorCountUpdater.incrementAndGet(this);
                throw e;
            }

            try {
                lock.lockInterruptibly();
            } catch (InterruptedException e) {
                connectErrorCountUpdater.incrementAndGet(this);
                throw new SQLException("interrupt", e);
            }

            try {
                if (!this.isFillable(toCount)) {
                    JdbcUtils.close(holder.getConnection());
                    LOG.info("fill connections skip.");
                    break;
                }
                this.putLast(holder, System.currentTimeMillis());
                fillCount++;
            } finally {
                lock.unlock();
            }
        }

        if (LOG.isInfoEnabled()) {
            LOG.info("fill " + fillCount + " connections");
        }

        return fillCount;
    }

    private boolean isFillable(int toCount) {
        int currentCount = this.poolingCount + this.activeCount;
        if (currentCount >= toCount || currentCount >= this.maxActive) {
            return false;
        } else {
            return true;
        }
    }

    public boolean isFull() {
        lock.lock();
        try {
            return this.poolingCount + this.activeCount >= this.maxActive;
        } finally {
            lock.unlock();
        }
    }

    private void emptySignal() {
        if (createScheduler == null) {
            empty.signal();
            return;
        }

        if (createTaskCount >= maxCreateTaskCount) {
            return;
        }

        if (activeCount + poolingCount + createTaskCount >= maxActive) {
            return;
        }
        submitCreateTask(false);
    }

    @Override
    public ObjectName preRegister(MBeanServer server, ObjectName name) throws Exception {
        if (server != null) {
            try {
                if (server.isRegistered(name)) {
                    server.unregisterMBean(name);
                }
            } catch (Exception ex) {
                LOG.warn("DruidDataSource preRegister error", ex);
            }
        }
        return name;
    }

    @Override
    public void postRegister(Boolean registrationDone) {

    }

    @Override
    public void preDeregister() throws Exception {

    }

    @Override
    public void postDeregister() {

    }

    public boolean isClosed() {
        return this.closed;
    }

    public boolean isCheckExecuteTime() {
        return checkExecuteTime;
    }

    public void setCheckExecuteTime(boolean checkExecuteTime) {
        this.checkExecuteTime = checkExecuteTime;
    }
}
