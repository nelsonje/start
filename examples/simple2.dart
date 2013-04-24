
//test multiple function calls
import 'stdio.dart';

void main()
{
  int x;

  if( 1 == 2 ) {
    x = 1;
  } else {
    if( 2 == 3 ) {
      x = 2;
      x = 4;
    } else {
      x = 3;
    }
  }

}
