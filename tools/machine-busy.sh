#!/usr/bin/env bash
# The share of the CPUs non-idle over the next two seconds, in percent,
# printed as one number: `BUSY=$(./machine-busy.sh)`.
#
# Written for orthotope's micro-regime3 benchmark and kept there until
# 2026-10-06, so the riders and run-evening.sh named below are that
# directory's, at
# https://github.com/Mikolaj/orthotope/tree/speedup-strided-tovector/micro-regime3
#
# The alarm the riders and run-evening.sh take before spending the
# machine, kept in one place since 2026-09-02 so that the two cannot
# disagree on what busy means. Two reads of /proc/stat two seconds apart
# measure what is running NOW and carry no history; a loadavg would still
# carry the sequence that has just ended, refusing the launch the
# procedure asks for while passing a box that got busy a minute ago. The
# bar is the caller's (MAXBUSY there, default 5); this only reads.
set -u
read -r _ u1 n1 s1 i1 w1 q1 f1 t1 _ < /proc/stat
sleep 2
read -r _ u2 n2 s2 i2 w2 q2 f2 t2 _ < /proc/stat
awk -v a="$((u1+n1+s1+i1+w1+q1+f1+t1))" -v b="$((u2+n2+s2+i2+w2+q2+f2+t2))" \
    -v ia="$((i1+w1))" -v ib="$((i2+w2))" \
  'BEGIN{d=b-a; if(d<=0){print "100.0"}else{printf "%.1f\n",100*(d-(ib-ia))/d}}'
