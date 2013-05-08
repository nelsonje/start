

import 'stdio.dart';

void other()
{
  int x;
  int y;
  x = 0;

  if( 1 == 1 ) {
      x = x + 1;
  }
}


void main()
{
  int x;
  int y;
  x = 0;

  if( 1 == 1 ) {
    if( 1 == 1 ) {
      x = x + 1;
      if( 1 == 1 ) {
        x = x + 1;
        other();
        x = x + 1;
      }
    }
  }

  WriteLong(x);
  WriteLong(y);
  WriteLine();
}
