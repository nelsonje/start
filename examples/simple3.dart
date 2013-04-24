

// example from paper figure 6
import 'stdio.dart';

void print( int i, int j, int k, int l ) {
  // nothing
  i = 0;
}

void main() {
  int i;
  int j;
  int k;
  int l;

  i = 1;
  j = 1;
  k = 1;
  l = 1;
  
  while( 1 == 0 ) {
    
    if( 1 == 1 ) {
      j = i;

      if( 1 == 1 ) {
        l = 2;
      } else {
        l = 3;
      }
      
      k = k + 1;
    } else {
      k = k + 2;
    }

    print( i, j, k, l );

    while( 1 == 0 ) {
      if( 1 == 1 ) {
        l = l + 4;
      }
    }

    i = i + 6;
  }
}
