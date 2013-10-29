#!/bin/bash
# Weiwei Jia <harryxiyou@gmail.com>
# Create directories and files oceanbase needs
rm -r /home/admin/oceanbase/data
mkdir -p /home/admin/oceanbase/data
mkdir -p /home/admin/oceanbase/data/rs
mkdir -p /home/admin/oceanbase/data/rs_commitlog
mkdir -p /home/admin/oceanbase/data/ups_commitlog
mkdir -p /home/admin/oceanbase/data/ups_data/raid0
mkdir -p /home/admin/oceanbase/data/ups_data/raid1
mkdir -p /home/admin/oceanbase/data/ups_data/raid2
mkdir -p /home/admin/oceanbase/data/ups_data/raid3
ln -s /data/1 /home/admin/oceanbase/data/ups_data/raid0/store0
ln -s /data/2 /home/admin/oceanbase/data/ups_data/raid0/store1
ln -s /data/3 /home/admin/oceanbase/data/ups_data/raid1/store0
ln -s /data/4 /home/admin/oceanbase/data/ups_data/raid1/store1
ln -s /data/5 /home/admin/oceanbase/data/ups_data/raid2/store0
ln -s /data/6 /home/admin/oceanbase/data/ups_data/raid2/store1
ln -s /data/7 /home/admin/oceanbase/data/ups_data/raid3/store0
ln -s /data/8 /home/admin/oceanbase/data/ups_data/raid3/store1
sudo rm -r /data
sudo mkdir /data
sudo chown admin /data
for disk in {1..8}; do mkdir -p /data/$disk/obtest/sstable; done;
for disk in {1..8}; do ln -s /data/$disk /home/admin/oceanbase/data/$disk; done;

# start oceanbase server
bin/rootserver -r 192.168.1.131:2500 -R 192.168.1.131:2500 -i eth0 -C 1
bin/updateserver -r 192.168.1.131:2500 -p 2700 -m 2701 -i eth0
bin/chunkserver -r 192.168.1.131:2500 -p 2600 -n obtest -i eth0
bin/mergeserver -r 192.168.1.131:2500 -p 2800 -z 2880 -i eth0
