/** Computes the factorial of x in y by iteratively decrementing
 * x and multiplying its values with y.
 */
factorial(mut x:int) -> (y:int) {
  y = 1;
  while (x != 1) {
    y = y * x;
    x = x - 1;
  }

  example {
    [x==0]
    -> y = 1;
  }
  
  example {
    [x==3]
    ->  y = 1;
    ->  y = y * x;
    ->  x = x - 1;
    ->  y = y * x;
    ->  x = x - 1;
  }
  
  test example {
    [x==1] -> ...
  }

  test example {
    [x==2] -> ...
  }
  
  test example {
    [x==4] -> ...
  }
  
  test example {
    [x==5] -> ...
  }
  
  test example {
    [x==6] -> ...
  }  

  test example {
    [x==7] -> ...
  }  

  test example {
    [x==8] -> ...
  }  

  test example {
    [x==9] -> ...
  }  

  test example {
    [x==10] -> ...
  }  

  test example {
    [x==11] -> ...
  }  
}
