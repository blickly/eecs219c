#!/usr/bin/env python

def xbuilder(n):
  def x(i, j):
    return (i - 1) * (n - 1) + j
  return x

def pigeonhole(n):
  x = xbuilder(n)
  nVars = n * (n-1)
  nClauses = n * (n-1) * (n-1) + n
  output =  "c Pigeon-hole sat problem (size=%d)\n" % n
  output += "p cnf %d %d\n" % (nVars, nClauses)
  for i in xrange(1,n+1):
    for j in xrange(1,n):
      output += "%d " % x(i,j)
    output += "0\n"
  for i in xrange(1,n+1):
    for j in xrange(1,n+1):
      for k in xrange(1,n):
        if i != j:
          output += "-%d -%d 0\n" % (x(i,k), x(j,k))
  return output

def main():
  for i in xrange(4,11):
    f = open("pigeon%d" % i, 'w')
    f.write(pigeonhole(i))
    f.close()

if __name__ == "__main__":
  main()
