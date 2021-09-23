tc qdisc add dev lo clsact

for prog in bpf_lb-DLB_L3.o bpf_lb-DLB_L4.o bpf_lb-DUNKNOWN.o; do
 tc filter add dev lo egress bpf da obj $prog sec from-netdev verb >& a1_$prog
 echo -ne $prog "\t"
 cat a1_$prog | grep "processed" | awk -e 'BEGIN { N = 0; }' -e '{ N += $2; }' -e 'END { print N; }'
 tc filter del dev lo egress
 rm -rf /sys/fs/bpf/tc/
done

tc filter add dev lo egress bpf da obj bpf_lxc-DDROP_ALL.o sec from-container verb >& a2
echo -ne bpf_lxc-DDROP_ALL.o"\t"
cat a2 | grep "processed" | awk -e 'BEGIN { N = 0; }' -e '{ N += $2; }' -e 'END { print N; }'
tc filter del dev lo egress
rm -rf /sys/fs/bpf/tc/

tc filter add dev lo egress bpf da obj bpf_lxc-DUNKNOWN.o sec from-container verb >& a3
echo -ne bpf_lxc-DUNKNOWN.o"\t"
cat a3 | grep "processed" | awk -e 'BEGIN { N = 0; }' -e '{ N += $2; }' -e 'END { print N; }'
tc filter del dev lo egress
rm -rf /sys/fs/bpf/tc/

tc filter add dev lo egress bpf da obj bpf_netdev.o sec from-netdev verb >& a4
echo -ne bpf_netdev.o"\t\t"
cat a4 | grep "processed" | awk -e 'BEGIN { N = 0; }' -e '{ N += $2; }' -e 'END { print N; }'
tc filter del dev lo egress
rm -rf /sys/fs/bpf/tc/

tc filter add dev lo egress bpf da obj bpf_overlay.o sec from-overlay verb >& a5
echo -ne bpf_overlay.o"\t\t"
cat a5 | grep "processed" | awk -e 'BEGIN { N = 0; }' -e '{ N += $2; }' -e 'END { print N; }'
tc filter del dev lo egress
rm -rf /sys/fs/bpf/tc/

tc filter add dev lo egress bpf da obj bpf_lxc_jit.o sec from-container verb >& a6
echo -ne bpf_lcx_jit.o"\t\t"
cat a6 | grep "processed" | awk -e 'BEGIN { N = 0; }' -e '{ N += $2; }' -e 'END { print N; }'
tc filter del dev lo egress
rm -rf /sys/fs/bpf/tc/

