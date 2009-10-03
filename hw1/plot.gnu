set terminal postscript eps enhanced color solid rounded
set output "plotname.eps"

sat1(x) = a * (exp(x) - 1)
sat2(x) = b * (exp(x) - 1)

fit sat1(x) "lz_sat1.dat" via a
fit sat2(x) "lz_sat2.dat" via b

plot "lz_sat1.dat", "lz_sat2.dat", sat1(x), sat2(x)
