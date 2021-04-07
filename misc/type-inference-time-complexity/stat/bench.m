dummyt = [0.67885
2.44208
5.22474
9.199
14.51163
22.82419
32.34955
40.75896
53.72458
69.26886];

dummyfunc = [18 38 58 78 98 118 138 158 178 198];

dummytype = [7602
16388
25930
35750
45590
55456
66306
77168
88006
98304];

dummyfuntype = [951
2239
3659
5002
6321
7622
8932
10242
11552
12862];

dummyfunt = [0.50272
1.10254
3.49156
7.57328
14.47544
24.32439
38.77991
58.61012
84.70287
117.16279];

dummyc = [29 59 89 119 149 179 209 239 269 299];

xval = linspace(10, 100, 10);

% createfigure(xval, [transpose(dummyfunt); transpose(dummyt)]);

% createfigure(xval, [dummyfunc; dummyc]);

createfigure(xval, [transpose(dummyfuntype); transpose(dummytype)]);
