#!/usr/bin/env ruby

require_relative "ILParser/ILParser"

print "Hello\n"

include ILParser
ILParser.foo()

print "Goodbye\n"
