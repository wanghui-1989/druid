package com.alibaba.druid;

import com.alibaba.druid.pool.DruidDataSource;
import com.alibaba.druid.pool.DruidDataSourceFactory;

import javax.sql.DataSource;
import java.sql.Connection;
import java.util.HashMap;
import java.util.Map;

/**
 * DruidDebugTest
 * Sep 27, 2020
 * @author wanghui
 */
public class DruidDebugTest {

    public static void main(String[] args) throws Exception {
        Map<String, String> map = new HashMap<String, String>();
        String url = "jdbc:mysql://com.example:3306/databasename";
        String username = "wang";
        String password = "123456";
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
