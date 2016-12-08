#!/bin/awk -f

BEGIN {
	srand();
	for(i = 0; i < 5000; i++)
		print int(5000*rand());
	exit;
}
