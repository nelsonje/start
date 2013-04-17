
# generate nested-if.dart with the appropriate amount of nesting
# usage: ruby nested-if.rb <total node count> <per-nest node count> > nested-if.dart
nodecount = ARGV[0].to_i
inedgecount = ARGV[1].to_i

if nodecount == 0
  nodecount = 2000
end

if inedgecount == 0
  inedgecount = 1
end

# count down
total = nodecount




puts """

import 'stdio.dart';

int n;
int result;

void main() {
result = 0;
"""

while total > 0

  if inedgecount > total
    inedgecount = total
  end

  # open nested if's
  puts "if( n > 0 ) {\n" * inedgecount

  # do something!
  puts "result = result + 1;\n"
  
  # close nested if's
  puts "}\n" * inedgecount

  total -= inedgecount

end
  
# end main()
puts """
}
"""


