On-disk Bitmap Index in PostgreSQL
=====================================
This repository has an on-disk bitmap index access method embeddedin PostgreSQL 8.3.23 kernel.

As is known to all, PostgreSQL official releases do not provide on-disk version bitmap index access method. This prevents many Postgres database addicts from testing bitmap index performance.

In fact, back to 2006 - 2008, Postgres Global Development Group were trying to implement this index and delivering it as a patch. However, afterwards, they gave up this plan and removed this prototype from the official Postgres release. The patch's source code is partially available at Greenplum Database and Postgres Community Mailing List and it relies on an unreleased version of Postgres which is between 8.2 and 8.3 (I have not figured it out). 

We combined the fragments of this on-disk bitmap index patch, modified them and implemented this index into PostgreSQL 8.3.23 offical release. Researchs now can play this bitmap index and try to compare it with any other indexes. 

Note that: the performance of this on-disk bitmap index patch is very unstable and not fully tested. The reliability is not guaranteed.

#Play around with Bitmap Index

For the ease of testing, we have implemented this on-disk Bitmap Index into PostgreSQL kernel (8.3.23) as one of the backend access methods. This verision is designed to be run on a Linux operating system.

## Download the source code
```
https://github.com/jiayuasu/bitmap-postgresql.git
```
## Build and Installation
Once you've synced with GitHub, the folder should contain the source code for PostgreSQL. The build and installation steps are exactly same with official PostgreSQL.

Note that: Due to some issues of GCC compiler, you have to use an old version of GCC (gcc 4.7 works for this) to compile the source code. Otherwise, the binary code won't work.


```
$ cd SourceFolder
$ ./configure
$ make
$ su
$ make install
$ adduser postgres
$ mkdir /usr/local/pgsql/data
$ chown postgres /usr/local/pgsql/data
$ su - postgres
$ /usr/local/pgsql/bin/initdb -D /usr/local/pgsql/data
$ /usr/local/pgsql/bin/postgres -D /usr/local/pgsql/data >logfile 2>&1 &
$ /usr/local/pgsql/bin/createdb test
$ /usr/local/pgsql/bin/psql test
```

## PostgreSQL Regression Test

After the installation, you have to make sure the source code on your machine pass all the PostgreSQL Regression Tests (115 in total).
```
$ cd SourceFolder

$ make check
```

## Usage in SQL

Here list some SQL commands of Bitmap index. For more details, please see the following Bitmap index test SQL script:
```
./src/test/regress/sql/bitmap_index.sql

```

### Build Bitmap Index
```
CREATE INDEX bitmap_idx ON bitmap_tbl USING bitmap(randomNumber);

```

### Query Bitmap Index

```
SELECT * FROM bitmap_tbl WHERE randomNumber = 1;
```

### Drop Bitmap Index
```
DROP INDEX bitmap_idx;
```
### Currently supported data type

Integer (stable), and most of the common data types in Postgres (unstable)

### Currently supported operator

```
<, <=, =, >=, >
```



For using Bitmap Index in PostgreSQL Regression Test Mode, you need to

* Read and change Bitmap index test SQL script:

```
./src/test/regress/sql/bitmap_index.sql

```
* View Bitmap index test SQL script output:

```
./src/test/regress/results/bitmap_index.out

```

* Modify Regression Test schedule if necessary

```
./src/test/regress/parallel_schedule
```
# Bitmap Index patch source code origins

[1] Postgres patch difference comparison result:

https://www.postgresql.org/message-id/attachment/19180/bitmap-4.diff

[2] Greeplum database Github source code:

https://github.com/greenplum-db/gpdb/tree/master/src/backend/access/bitmap

[3] Postgres Gloabl Developement Group discussion:

https://www.postgresql.org/message-id/Pine.LNX.4.58.0705031335240.10105@linuxworld.com.au

[4] Bitmap Index main idea from Postgres Wiki

https://wiki.postgresql.org/wiki/Bitmap_Indexes



# Contact

Only for bitmap index patch integration issues

## Contributors
* [Jia Yu](http://www.public.asu.edu/~jiayu2/) (Email: jiayu2@asu.edu)

* [Mohamed Sarwat](http://faculty.engineering.asu.edu/sarwat/) (Email: msarwat@asu.edu)

## DataSys Lab
[DataSys Lab](http://www.datasyslab.org/) at Arizona State University aims at designing and developing experimental data management systems (e.g., database systems).

***
PostgreSQL Database Management System
=====================================
  
This directory contains the source code distribution of the PostgreSQL
database management system.

PostgreSQL is an advanced object-relational database management system
that supports an extended subset of the SQL standard, including
transactions, foreign keys, subqueries, triggers, user-defined types
and functions.  This distribution also contains C language bindings.

PostgreSQL has many language interfaces including some of the more
common listed below:

C++ - http://pqxx.org/development/libpqxx/
JDBC - http://jdbc.postgresql.org
ODBC - http://odbc.postgresql.org
Perl - http://search.cpan.org/~dbdpg/
PHP - http://www.php.net
Python - http://www.initd.org/
Ruby - http://ruby.scripting.ca/postgres/

Other language binding are available from a variety of contributing
parties.

PostgreSQL also has a great number of procedural languages available,
a short, incomplete list is below:

PL/pgSQL - included in PostgreSQL source distribution
PL/Perl - included in PostgreSQL source distribution
PL/PHP - http://projects.commandprompt.com/projects/public/plphp
PL/Python - included in PostgreSQL source distribution
PL/Java - http://pgfoundry.org/projects/pljava/
PL/Tcl - included in PostgreSQL source distribution

See the file INSTALL for instructions on how to build and install
PostgreSQL.  That file also lists supported operating systems and
hardware platforms and contains information regarding any other
software packages that are required to build or run the PostgreSQL
system.  Changes between all PostgreSQL releases are recorded in the
file HISTORY.  Copyright and license information can be found in the
file COPYRIGHT.  A comprehensive documentation set is included in this
distribution; it can be read as described in the installation
instructions.

The latest version of this software may be obtained at
http://www.postgresql.org/download/.  For more information look at our
web site located at http://www.postgresql.org/.

