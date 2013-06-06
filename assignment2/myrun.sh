#echo const
#/usr/local/bin/ruby main.rb ../examples/const.dart.il
#echo class
#/usr/local/bin/ruby main.rb ../examples/class.dart.il
#echo gcd
#/usr/local/bin/ruby main.rb ../examples/gcd.dart.il
#echo hanoi
#/usr/local/bin/ruby main.rb ../examples/hanoifibfac.dart.il
#echo link
#/usr/local/bin/ruby main.rb ../examples/link.dart.il
#echo loop
#/usr/local/bin/ruby main.rb ../examples/loop.dart.il
echo mmm
/usr/local/bin/ruby main.rb ../examples/mmm.dart.il -opt=ssa,profile -backend=ssa
#echo points
#/usr/local/bin/ruby main.rb ../examples/points.dart.il
#echo prime
#/usr/local/bin/ruby main.rb ../examples/prime.dart.il
#echo MYregslarge
#/usr/local/bin/ruby main.rb ../examples/myregslarge.dart.il
#echo sieve
#/usr/local/bin/ruby main.rb ../examples/sieve.dart.il
#echo sort
#/usr/local/bin/ruby main.rb ../examples/sort.dart.il
#echo struct
#/usr/local/bin/ruby main.rb ../examples/struct.dart.il

