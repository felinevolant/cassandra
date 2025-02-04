/*
 * Licensed to the Apache Software Foundation (ASF) under one
 * or more contributor license agreements.  See the NOTICE file
 * distributed with this work for additional information
 * regarding copyright ownership.  The ASF licenses this file
 * to you under the Apache License, Version 2.0 (the
 * "License"); you may not use this file except in compliance
 * with the License.  You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package org.apache.cassandra.distributed.test;

import java.io.IOException;
import java.nio.ByteBuffer;
import java.nio.charset.StandardCharsets;
import java.util.List;

import org.junit.Test;

import com.datastax.driver.core.ProtocolVersion;
import com.datastax.driver.core.ResultSet;
import com.datastax.driver.core.Session;
import org.apache.cassandra.distributed.Cluster;
import org.apache.cassandra.distributed.api.Feature;
import org.apache.cassandra.distributed.api.IInvokableInstance;
import org.assertj.core.api.Assertions;

import static org.apache.cassandra.config.CassandraRelevantProperties.IO_NETTY_EVENTLOOP_THREADS;

public class NativeMixedVersionTest extends TestBaseImpl
{
    @Test
    public void v4ConnectionCleansUpThreadLocalState() throws IOException
    {
        // make sure to limit the netty thread pool to size 1, this will make the test determanistic as all work
        // will happen on the single thread.
        IO_NETTY_EVENTLOOP_THREADS.setInt(1);
        try (Cluster cluster = Cluster.build(1)
                                      .withConfig(c ->
                                                  c.with(Feature.values())
                                                   .set("read_thresholds_enabled", true)
                                                   .set("local_read_size_warn_threshold", "1KiB")
                                      )
                                      .start())
        {
            init(cluster);
            cluster.schemaChange(withKeyspace("CREATE TABLE %s.tbl (pk int, ck1 int, value blob, PRIMARY KEY (pk, ck1))"));
            IInvokableInstance node = cluster.get(1);

            ByteBuffer blob = ByteBuffer.wrap("This is just some large string to get some number of bytes".getBytes(StandardCharsets.UTF_8));

            for (int i = 0; i < 100; i++)
                node.executeInternal(withKeyspace("INSERT INTO %s.tbl (pk, ck1, value) VALUES (?, ?, ?)"), 0, i, blob);

            // v4+ process STARTUP message on the netty thread.  To make sure we do not leak the ClientWarn state,
            // make sure a warning will be generated by a query then run on the same threads on the v3 protocol (which
            // does not support warnings)
            try (com.datastax.driver.core.Cluster driver = JavaDriverUtils.create(cluster, ProtocolVersion.V5);
                 Session session = driver.connect())
            {
                ResultSet rs = session.execute(withKeyspace("SELECT * FROM %s.tbl"));
                Assertions.assertThat(rs.getExecutionInfo().getWarnings()).isNotEmpty();
            }

            try (com.datastax.driver.core.Cluster driver = JavaDriverUtils.create(cluster, ProtocolVersion.V3);
                 Session session = driver.connect())
            {
                ResultSet rs = session.execute(withKeyspace("SELECT * FROM %s.tbl"));
                Assertions.assertThat(rs.getExecutionInfo().getWarnings()).isEmpty();
            }

            // this should not happen; so make sure no logs are found
            List<String> result = node.logs().grep("Warnings present in message with version less than").getResult();
            Assertions.assertThat(result).isEmpty();
        }
        finally
        {
            IO_NETTY_EVENTLOOP_THREADS.clearValue();
        }
    }
}
