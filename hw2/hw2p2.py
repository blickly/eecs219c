#!/usr/bin/env python

import sys
import os
import shutil

def main():
  smtfile = sys.argv[1]
  iterations = sys.argv[2]
  for i in xrange(int(iterations)):
    assumption = iteration(smtfile)
    if assumption == None:
      print "Finished after %d iterations" % i
      return
    addassumption(smtfile, 'newfile.smt', assumption)
    shutil.move('newfile.smt', smtfile)

def addassumption(oldfile, newfile, assumption):
  nf = open(newfile, "w")
  done = False
  for line in open(oldfile, "r"):
    if ":formula" in line and not done:
      nf.write(":assumption %s\n" % assumption)
      done = True
    nf.write(line)
  nf.close()

def iteration(smtfile):
  os.system("beaver --sat-solver abc -m %s" % smtfile)
  modelfilename = smtfile.rstrip("smt") + "model"
  if not os.path.exists(modelfilename):
    return
  negation = parsemodel(modelfilename)
  return negation

def parsemodel(filename):
  assertion = "(or "
  for line in open(filename, "r"):
    (lhs, _, rhs) = line.rstrip("\n").partition(" = ")
    if rhs == "true":
      assertion += "(not %s)" % lhs
    elif rhs == "false":
      assertion += "%s" % lhs
    else:
      assertion += "(not (= %s %s))" % (lhs, rhs)
  assertion += ")"
  return assertion

if __name__ == "__main__":
  main()
