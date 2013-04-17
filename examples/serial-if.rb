
# generate serial-if.dart with the appropriate amount of nesting

nodecount = ARGV[0].to_i

puts """

import 'stdio.dart';

int n;
int result;

void main() {
result = 0;
"""

# open nested if's
puts """
  if( n > 0 ) { }""" * nodecount

# do something!
puts """
  result = result + 1;"""

# end main()
puts """
}
"""


