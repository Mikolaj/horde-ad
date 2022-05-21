set cbrange [0:1]

stats "/tmp/foo/all.dat"

set term gif animate delay 10 loop -1

set output "/tmp/foo.gif"

do for [i=1:int(STATS_blocks)] { plot '/tmp/foo/all.dat' index (i-1) with image, "/tmp/foo/points.dat" }
