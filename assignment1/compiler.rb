#!/usr/bin/env ruby


# CSE 501 compiler project
# requires ruby 1.9

require 'trollop'
require 'minitest/benchmark' if ENV["BENCH"]

# parse options
opts = Trollop::options do
  opt :filename, "IL file to process", :type => String, :default => 'test1.il'
end


class Type
  attr_accessor :name, :members

  def initialize( line )
    fields = line.split(' ')

    @name = fields[1].chomp(':')

    @members = Array.new
    typestring = line.gsub(/.*: /,'')
    typestring.split(' ').each do |memberstring|
      elems = memberstring.split(/[#:]/)
      @members.push( { :name => elems[0], 
                       :offset => elems[1].to_i,
                       :type => elems[2] } )
      puts "creating new Type #{@name} with members #{@members}"
    end
  end
end

class Method
  attr_accessor :name, :args
  
  def initialize( name, typestring )
    fields = line.split(' ')

    @name = fields[1].chomp(':')

    @members = Array.new
    typestring = line.gsub(/.*: /,'')
    typestring.split(' ').each do |memberstring|
      elems = memberstring.split(/[#:]/)
      @members.push( { :name => elems[0], 
                       :offset => elems[1].to_i,
                       :type => elems[2] } )
      puts "creating new Type #{@name} with members #{@members}"
    end

    @name = name
  end
end


# storage
types = Array.new
methods = Array.new
globals = Array.new
instructions = Array.new



# parse file
IO.foreach( opts[:filename] ) do |line|

  fields = line.split(' ')

  # what's the opcode?
  case fields[0]

  when 'type'
    type = Type.new( line )
    types.push( type )
    
  when 'method'
    puts "found method #{fields[1]}"

  when 'global'
    puts "found global #{fields[1]}"

  when 'instr'
    puts "found instr #{fields[2]}"

  else
    raise 'unknown opcode'

  end

end
