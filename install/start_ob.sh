#!/bin/bash
# Weiwei Jia <harryxiyou@gmail.com>
# start oceanbase server
bin/rootserver -r 192.168.1.131:2500 -R 192.168.1.131:2500 -i eth0 -C 1
sleep 10
bin/updateserver -r 192.168.1.131:2500 -p 2700 -m 2701 -i eth0
sleep 10
bin/chunkserver -r 192.168.1.131:2500 -p 2600 -n obtest -i eth0
sleep 10
bin/mergeserver -r 192.168.1.131:2500 -p 2800 -z 2880 -i eth0

# initialize oceanbase
bin/rs_admin -r 192.168.1.131 -p 2500 set_obi_role -o OBI_MASTER
bin/rs_admin -r 192.168.1.131 -p 2500 -t 60000000 boot_strap
