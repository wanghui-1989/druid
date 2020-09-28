package com.alibaba.druid;

import com.alibaba.druid.pool.DruidDataSource;
import com.alibaba.druid.pool.DruidDataSourceFactory;

import javax.sql.DataSource;
import java.sql.Connection;
import java.util.HashMap;
import java.util.Map;

/**
 * DruidTestMain
 * Sep 27, 2020
 * @author wanghui
 */
public class DruidTestMain {

    public static void main(String[] args) throws Exception {
        Map<String, String> map = new HashMap<String, String>();
        String url = "jdbc:mysql://hx-hfe_hts-HFE_HTS-master.db.tuniu-sit.org:3306/hfe_hts";
        String username = "HFE_HTS_rw";
        String password = "tuniu520";
        String driverClass = "com.mysql.jdbc.Driver";

        map.put("driverClass", driverClass);
        map.put("url", url);
        map.put("username", username);
        map.put("password", password);
        map.put("filters", "slf4j");

        DruidDataSource dataSource = (DruidDataSource) DruidDataSourceFactory.createDataSource(map);
        Connection connection = dataSource.getConnection();
        System.out.println(connection);


    }

}
