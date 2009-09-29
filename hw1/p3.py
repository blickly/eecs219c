#!/usr/bin/env python

def xbuilder(n):
  def x(i, j):
    return (i - 1) * (n - 1) + j
  return x

def pigeonhole(n):
  x = xbuilder(n)
  clauses = ""
  nClauses = 0
  for i in xrange(1,n+1):
    for j in xrange(1,n):
      clauses += "%d " % x(i,j)
    clauses += "0\n"
    nClauses += 1
  for i in xrange(1,n+1):
    for j in xrange(1,n+1):
      for k in xrange(1,n):
        if i != j:
          clauses += "-%d -%d 0\n" % (x(i,k), x(j,k))
          nClauses += 1
  nVars = n * (n-1)
  clauses = ("c Pigeon-hole sat problem (size=%d)\n" % i
           + "p cnf %d %d\n" % (nVars, nClauses)
           + clauses )
  return clauses

def main():
  for i in xrange(4,11):
    f = open("pigeon%d" % i, 'w')
    f.write(pigeonhole(i))
    f.close()

if __name__ == "__main__":
  main()
