SET enable_seqscan = OFF;
SET enable_indexscan = ON;
SET enable_bitmapscan = ON;

create table bm_test (i int, t text);
insert into bm_test select i % 10, (i % 10)::text  from generate_series(1, 100) i;
create index bm_test_idx on bm_test using bitmap (i);
select count(*) from bm_test where i=1;
select * from bm_test where i > 10;
reindex index bm_test_idx;
select count(*) from bm_test where i=1;
select * from bm_test where i > 10;
drop index bm_test_idx;
drop table bm_test;

