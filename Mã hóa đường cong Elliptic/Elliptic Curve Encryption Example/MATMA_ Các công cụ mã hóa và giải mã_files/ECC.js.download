// multiply a value to the current value and return the sum
// retur// accumulate values to put into text area
var accumulated_output_info="";

// indent of what we are displaying (nested subroutines)
var cur_indent = "";

// define variables before we use them
var ECC_GFp_p, ECC_GFp_a, ECC_GFp_b, ECC_GFp_G, ECC_GFp_n,
   ECC_GFp_h, ECC_GFp_d, ECC_GFp_Q;
var ECC_GF2m_F, ECC_GF2m_a, ECC_GF2m_b, ECC_GF2m_G, ECC_GF2m_n,
   ECC_GF2m_h, ECC_GF2m_d, ECC_GF2m_Q;

// group GF(p)

//----------------------------------
//   Galois Field GF(p)
//----------------------------------

// add a value to the current value and return the sum
// return the new value
function GFp_add( num1, num2 )
{
   return ( this.p + num1 + num2 ) % this.p;
}

// subtract a value from the current value and return the sum
// return the new value
function GFp_sub( num1, num2 )
{
   return ( this.p + num1 - num2 ) % this.p;
}

function GFp_mul( num1, num2 )
{
   return ( num1 * num2 ) % this.p;
}

// Divide two values in GF(p)
// use the precomputed inverse table
function GFp_div( num1, num2 )
{
   return ( num1 * this.inverse_table[num2] ) % this.p;
}

// create a group GF(p)
function GFp( p )
{
   this.p = p;
   this.add = GFp_add;
   this.sub = GFp_sub;
   this.mul = GFp_mul;
   this.div = GFp_div;

   // create the multiplicative inverses
   this.inverse_table = new Array(p);

   this.inverse_table[0] = 0;

   // generate the inverses
   // use brute force to find i*j=1 (mod p)
   //  (assumes p is small)!!!!!
   for ( var i=1; i<p; i++ )
      for ( var j=1; j<p; j++ )
         if ( ((i*j)%p) == 1 )
         {
            this.inverse_table[i] = j;
            break;            // done here
         }
}

//----------------------------------
//   Galois Field GF(2^m)
//----------------------------------

// format a polynomial
function GF2m_format_poly( poly )
{
   var res;
   if ( poly < 16 )
      res = "0" + poly.toString(16);
   else
      res = poly.toString( 16 );
   
   res += " (";
   
   // zero poly?
   if ( poly == 0 )
      return "00 (0)";
   
   var first_term=true;
   var i;
   for( i=30; i>=0; i-- )
   {
      if ( (poly & (1<<i)) != 0 )
      {
         if ( first_term )
            first_term = false;
         else
            res += " + ";
      
         if ( i>=2 )
            res += "g^" + i;
         else if ( i==1 )
            res += "g";
         else
            res += "1";
      }
   }

   return res + ")";
}

// add a value to the current value and return the sum
// return the new value
function GF2m_add( num1, num2 )
{
   return num1 ^ num2;
}

// what is the highest exponent in this polynomial?
// return largest k for x^k term not zero or -1
function GF2m_poly_order( poly )
{
   for( var i=30; i>=0; i-- )
      if ( (poly & (1<<i)) != 0 )
         return i;

   // polynomial must be 0
   return -1;
}

// multiply a value to the current value and return the sum
// return the new value
function GF2m_mul( num1, num2 )
{
   var i;

   // multiply the values first
   var res = 0;
   for( i=0; i<=this.m; i++ )
      if ( (num1 & (1<<i)) != 0 )
         res ^= num2 << i;

   // now take the remainder after dividing by the polynomial
   // try dividing the product by the group's polynomial
   var res_order = GF2m_poly_order(res);

   while( res_order >= this.poly_order )
   {
      // save order for later sanity check
      var x = res_order;

      // shift divisor and 'subtract'
      res ^= this.poly << (res_order-this.poly_order);

      // what is the new order
      res_order = GF2m_poly_order(res);

      // no drop (should never occur)?
      if ( x <= res_order )
      {
         window.alert("No drop in poly order!!!");
         return 0;
      }
   }

   // send back our final result
   return res;
}

// Divide two values in GF(p)
// use the precomputed inverse table
function GF2m_div( num1, num2 )
{
   return this.mul( num1, this.inverse_table[num2] );
}

// create a group GF(2^m)
function GF2m( m, p )
{
   this.m = m;
   this.two_m = 1<<m;      // 2^m
   this.poly = p;
   this.poly_order = GF2m_poly_order(p);
   this.one = 1;
   this.add = GF2m_add;
//   this.sub = GF2m_add;  // both add and subtract become XOR
   this.mul = GF2m_mul;
   this.div = GF2m_div;
   
   // create the multiplicative inverses
   this.inverse_table = new Array(this.two_m);
   this.inverse_table[0] = 0;
   this.inverse_table[1] = 1;
     
   // fill in values for tables

   // generate the inverses
   //calculate inverses by computing x^n for n=1..126, then
   // knowing that x^p * x^q == 1 if p+q = 127
   var temp_array = new Array( 128 );
   
   //  (assumes fields are small)!!!!!
   var x_i = 1;
   var i;
   temp_array[0]=0;
   for ( i=1; i<this.two_m; i++ )
   {
      // insert another power of x
      x_i = this.mul( x_i, 2 );
      // save x^i
      temp_array[i] = x_i;
   }
   
   // now use arrays to build inverse table,
   //    remembering   x^p * x^q == 1 if p+q = 127
   for ( i=1; i<this.two_m-1; i++ )
   {
      var p1 = temp_array[i];
      var p2 = temp_array[ (this.two_m-1) - i ];
      
      this.inverse_table[p1] = p2;
      this.inverse_table[p2] = p1;
   }
}

//----------------------------------
//   Elliptic curve over GF(p)
//----------------------------------

// note we use y=-1 for the zero point
function ECC_GFp_is_zero()
{
   if ( this.x == 0 && this.y == 0 )
      return true;
   else
      return false;
}

// add two distinct points on the curve
// p2 is the ECC_GFp_Point to add to the current point
// return the sum of the points
function ECC_GFp_add_distinct( p2 )
{
   var save_indent = cur_indent;
   cur_indent += "  ";
 
   // do we have additive inverses (return zero)?
   if ( this.x == p2.x && this.y == -p2.y )
   {
      cur_indent = save_indent;
      return new ECC_GFp_Point( 0, 0 );
   }
   
   // calculate the slope between the two points
   //   lambda = (y2-y1)/(x2-x1)
   var temp1 = ECC_GFp_p.sub( p2.y, this.y );
   accumulated_output_info += cur_indent + "y2-y1 = " + temp1 + "\n";
   var temp2 = ECC_GFp_p.sub( p2.x, this.x );
   accumulated_output_info += cur_indent + "x2-x1 = " + temp2 + "\n";
   var lambda = ECC_GFp_p.div( temp1, temp2 );
   accumulated_output_info += cur_indent + "lambda = (y2-y1)/(x2-x1) = " + lambda + "\n";
   
   // calculate the resulting point
   // x3 = lambda*lambda - this.x - p2.x;
   temp1 = ECC_GFp_p.mul( lambda, lambda );
   accumulated_output_info += cur_indent + "lambda^2 = " + temp1 + "\n";
   temp2 = ECC_GFp_p.sub( temp1, this.x );
   var x_res = ECC_GFp_p.sub( temp2, p2.x );
   accumulated_output_info += cur_indent + "x3 = lambda - x1 - x2 = " + x_res + "\n";
   
   // y3 = lambda * ( this.x - x_res ) - this.y;
   temp1 = ECC_GFp_p.sub( this.x, x_res );
   accumulated_output_info += cur_indent + "x1-x3 = " + temp1 + "\n";
   temp2 = ECC_GFp_p.mul( lambda, temp1 );
   accumulated_output_info += cur_indent + "lambda*(x1-x3) = " + temp2 + "\n";
   var y_res = ECC_GFp_p.sub( temp2, this.y );
   accumulated_output_info += cur_indent + "y3 = lambda*(x1-x3)-y1 = " + y_res + "\n";
   
   cur_indent = save_indent;
   
   return new ECC_GFp_Point( x_res, y_res );
}

// add a point to itself
// return the resulting point
function ECC_GFp_double()
{
   var save_indent = cur_indent;
   cur_indent += "  ";

   // lambda = ( 3 * x^2 + a ) / (2*y)
   var temp1 = ECC_GFp_p.mul( this.x, this.x );
   accumulated_output_info += cur_indent + "x1^2 = " + temp1 + "\n";
   var three_xsquared = ECC_GFp_p.mul( 3, temp1 );
   accumulated_output_info += cur_indent + "3*x1^2 = " + three_xsquared + "\n";
   var temp2 = ECC_GFp_p.add( three_xsquared, ECC_GFp_a );
   accumulated_output_info += cur_indent + "3*x1^2+a = " + temp2 + "\n";
   var temp3 = ECC_GFp_p.mul( 2, this.y );
   accumulated_output_info += cur_indent + "2*y1 = " + temp3 + "\n";
   var lambda = ECC_GFp_p.div( temp2, temp3 );
   accumulated_output_info += cur_indent + "lambda = (3*x1^2+a)/(2*y1) = " + lambda + "\n";
   
   // calculate the resulting point
   // x3 = lambda*lambda - x - x;
   temp1 = ECC_GFp_p.mul( lambda, lambda );
   accumulated_output_info += cur_indent + "lambda^2 = " + temp1 + "\n";
   temp2 = ECC_GFp_p.sub( temp1, this.x );
   var x_res = ECC_GFp_p.sub( temp2, this.x );
   accumulated_output_info += cur_indent + "x3 = lambda^2-x1-x1 = " + x_res + "\n";
   
   // y3 = lambda * ( this.x - x_res ) - this.y;
   temp1 = ECC_GFp_p.sub( this.x, x_res );
   accumulated_output_info += cur_indent + "x1-x3 = " + temp1 + "\n";
   temp2 = ECC_GFp_p.mul( lambda, temp1 );
   accumulated_output_info += cur_indent + "lambda*(x1-x3) = " + temp2 + "\n";
   var y_res = ECC_GFp_p.sub( temp2, this.y );
   accumulated_output_info += cur_indent + "y3 = lambda*(x-x3)-x1 = " + y_res + "\n";

   cur_indent = save_indent;  
   return new ECC_GFp_Point( x_res, y_res );
}

// generic add
function ECC_GFp_add( p2 )
{
   var add_result;
   
   // indent one more level
   var save_indent = cur_indent;
   cur_indent += "  ";
   accumulated_output_info += cur_indent + "Adding " + this.format() + " and " + p2.format() + "\n";
   
   // is this zero?
   if ( this.is_zero() )
   {
      add_result = p2;
   }
   // is the other number zero?
   else if ( p2.is_zero() )
   {
      add_result = this;
   }
   // identical points?
   else if ( this.x==p2.x && this.y == p2.y )
   {
      add_result = this.ECC_GFp_double();
   }   
   // inverses?
   else if ( this.x == p2.x && ((this.y+p2.y)%ECC_GFp_p.p) == 0 )
   {
      add_result = new ECC_GFp_Point( 0, 0 );
   }
   else
   {
      // otherwise add different points
      add_result = this.ECC_GFp_add_distinct( p2 );
   }

   accumulated_output_info += cur_indent + "Sum is " + add_result.format() + "\n";
   cur_indent = save_indent;
 
   return add_result;
}

// invert a point (x,-y) mod p
function ECC_GFp_invert()
{
   if ( this.is_zero() )
      return this;
   
   // negate the y value
   var inverse = new ECC_GFp_Point( this.x, ECC_GFp_p.sub( 0, this.y ) );
   accumulated_output_info += cur_indent + "  Inverse of " + this.format() + " is " + inverse.format() + "\n";
 
   return inverse;
}

// scalar multiply
// n*P = P + P + P + ... + P
// assume n >= 2
function ECC_GFp_scalar_mul( n )
{
   // indent one more level
   var save_indent = cur_indent;
   accumulated_output_info += cur_indent + "Scalar Multiply: " + n + "*" + this.format() + "\n";
   cur_indent += "  ";

   if ( this.is_zero() )
   {
      accumulated_output_info += cur_indent + "Returning Zero\n";
      cur_indent = save_indent;
      return this;
   }
   
   // start with 0
//   var res = this;
//   document.write( "-- ECC_GFp_smul, n=" + n + ", point=" + this.format() + ", double=" + res.format() + "<BR>" );
   
   // finish the additions
//   for( var i=1; i<n; i++ )
//   {
//      res = res.add( this );
//      document.write( "-- ECC_GFp_smul, i=" + i + ", res=" + res.format() + "<BR>" );
//   }
  
   // use double and add approach
   var res = new ECC_GFp_Point( 0, 0 );     // start with zero point
   var res_mul=0;                   // res = __ * P
   var P2n = this;                    // copy the starting point
   var P2n_mul = 1;                 // G2n = __ * P
   while( true )
   {
      if ( (n&1) == 1 )             // have a 1 bit here?
      {
         accumulated_output_info += cur_indent + "Calculating " +
                  (res_mul+P2n_mul) + "*" + this.format() + " = " +
                  res_mul + "*" + this.format() + " + " +
                  P2n_mul + "*" + this.format() + " = " +
                  res.format() + " + " + P2n.format() + "\n";
         
         res_mul += P2n_mul;        // update result multiplier
         res = res.add( P2n );            // add the current 2^n * P
         accumulated_output_info += cur_indent + "Working result: " + res_mul +
                     "*" + this.format() + " = " + res.format() + "\n";
      }
      
      if ( n <= 1 )
         break;
      
      // double P
      accumulated_output_info += cur_indent + "Doubling " +
                  P2n_mul + "*" + this.format() + " = " + P2n.format() + "\n";
      P2n = P2n.ECC_GFp_double();             // get 2^(n+1) P (double it)
      P2n_mul *= 2;                 // update our multiplier
      accumulated_output_info += cur_indent + "Double value: " + P2n_mul + "*" +
                     this.format() + " = " + P2n.format() + "\n";
      
      n = n >> 1;                   // halve n
   }
   
   accumulated_output_info += cur_indent + "Product is " + res.format() + "\n";
   cur_indent = save_indent;
  
   return res;
}

// format for display
function ECC_GFp_format()
{
   // do we have the zero point?
   if ( this.is_zero() )
      return "(Zero)";
   
   // not zero, display point
   return "(" + this.x + "," + this.y + ")";
}

// create a point on the curve
function ECC_GFp_Point( x, y )
{
   this.x = x;
   this.y = y;
   this.add = ECC_GFp_add;
//   this.invert = ECC_GFp_invert;
   this.smul = ECC_GFp_scalar_mul;
   this.format = ECC_GFp_format;
   this.is_zero = ECC_GFp_is_zero;
   this.invert = ECC_GFp_invert;
   // put in for subfunction use
   this.ECC_GFp_double = ECC_GFp_double;
   this.ECC_GFp_add_distinct = ECC_GFp_add_distinct;
}
  
// base set of values for the ECC curve
// p = prime we are using
// a, b = coordinates for the curve (y^2 = x^3 + ax + b)
// G = generator point
// n = order of the point
// h = ratio to # of points and order

// sample curves
// p= 67, a= 2, b=  3, G=(2,22),  n= 14, h=4
// p= 67, a= 2, b=  3, G=(3,6),   n= 28, h=2
// p= 67, a= 1, b=  3, G=(6,15),  n= 65, h=1
// p= 71, a= 1, b=  3, G=(1,17),  n= 32, h=2
// p= 71, a= 1, b=  5, G=(2,21),  n= 17, h=4
// p= 71, a=-2, b= -3, G=(2,1),   n= 67, h=1
// p= 71, a= 4, b= -6, G=(2,9),   n= 73, h=1
// p=751, a=-1, b=188, G=(0,376), n=727, h=1
ECC_GFp_p = new GFp( 71 );
ECC_GFp_a = 4;
ECC_GFp_b = -6;
ECC_GFp_G = new ECC_GFp_Point( 2, 9 );
ECC_GFp_n = 73;
ECC_GFp_h = 1;

// private key
ECC_GFp_d = 7;

// last part of public key Q=d*G = (38,63)
ECC_GFp_Q = ECC_GFp_G.smul( ECC_GFp_d );
//window.alert("Q="+ECC_GFp_Q.format() );

// display the GF(p) curve
function print_ECC_GFp()
{
   document.write( "Public Key: p=" + ECC_GFp_p.p );
   document.write( ", a=" + ECC_GFp_a );
   document.write( ", b=" + ECC_GFp_b );
   document.write( ", G=" + ECC_GFp_G.format() );
   document.write( ", Q=" + ECC_GFp_Q.format() );
   document.write( ", n=" + ECC_GFp_n );
   document.write( ", h=" + ECC_GFp_h );
   document.write( "<BR>Private key: d=" + ECC_GFp_d );
}

//----------------------------------
//  Elliptic Curve over GF(2^m)
//----------------------------------

// note we use y=-1 for the zero point
function ECC_GF2m_is_zero()
{
   if ( this.x == 0 && this.y == 0 )
      return true;
   else
      return false;
}

// add two distinct points on the curve
// p2 is the ECC_GF2m_Point to add to the current point
// return the sum of the points
function ECC_GF2m_add_distinct( p2 )
{
   var save_indent = cur_indent;
   cur_indent += "  ";

   // do we have additive inverses (return zero)?
   if ( this.x == p2.x && this.y == -p2.y )
   {
      cur_indent = save_indent;
      return new ECC_GF2m_Point(0,0);
   }
   
   // calculate the slope between the two points
   //   lambda = (y2+y1)/(x2+x1)
   var temp1 = ECC_GF2m_F.add( p2.y, this.y );
   accumulated_output_info += cur_indent + "y2+y1 = " + GF2m_format_poly(temp1) + "\n";
   var temp2 = ECC_GF2m_F.add( p2.x, this.x );
   accumulated_output_info += cur_indent + "x2+x1 = " + GF2m_format_poly(temp2) + "\n";
   var lambda = ECC_GF2m_F.div( temp1, temp2 );
   accumulated_output_info += cur_indent + "lambda = (y2+y1)/(x2+x1) = " + GF2m_format_poly(lambda) + "\n";
   
   // calculate the resulting point
   // x3 = lambda*lambda + lambda + this.x + p2.x + a;
   var x_res = ECC_GF2m_F.mul( lambda, lambda );
   x_res = ECC_GF2m_F.add( x_res, lambda );
   x_res = ECC_GF2m_F.add( x_res, this.x );
   x_res = ECC_GF2m_F.add( x_res, p2.x );
   x_res = ECC_GF2m_F.add( x_res, ECC_GF2m_a );
   // y3 = lambda * ( this.x + x3 ) + x3 + this.y;
   var y_res = ECC_GF2m_F.add( this.x, x_res );
   y_res = ECC_GF2m_F.mul( lambda, y_res );
   y_res = ECC_GF2m_F.add( y_res, x_res );
   y_res = ECC_GF2m_F.add( y_res, this.y );
   
   cur_indent = save_indent;
   return new ECC_GF2m_Point( x_res, y_res );
}

// add a point to itself
// return the resulting point
function ECC_GF2m_double()
{
   //   lambda = (x + y)/x
   var lambda = ECC_GF2m_F.add( this.x, ECC_GF2m_F.div(  this.y, this.x ) );

   // calculate the resulting point
   // x3 = lambda*lambda + lambda + a;
   var x_res = ECC_GF2m_F.mul( lambda, lambda );
   x_res = ECC_GF2m_F.add( x_res, lambda );
   x_res = ECC_GF2m_F.add( x_res, ECC_GF2m_a );

   // y3 = this.x^2 + (lambda+1) * x_res;
   var y_res = ECC_GF2m_F.mul( this.x, this.x );
   var temp  = ECC_GF2m_F.add( lambda, 1 );
   temp = ECC_GF2m_F.mul( temp, x_res );
   y_res = ECC_GF2m_F.add( y_res, temp );

   return new ECC_GF2m_Point( x_res, y_res );
}

// generic add
function ECC_GF2m_add( p2 )
{
   var add_result;
     
   // is this zero?
   if ( this.is_zero() )
   {
      add_result = p2;
   }
   // is the other number zero?
   else if ( p2.is_zero() )
   {
      add_result = this;
   }
   // identical points?
   else if ( this.x==p2.x && this.y == p2.y )
   {
      add_result = this.ECC_GF2m_double();
   }
   // note: no check for  this.y == -p2.y in GF(2^m) since y=-y for all y
   else
   {
      // otherwise add different points
      add_result = this.ECC_GF2m_add_distinct( p2 );
   }
 
   return add_result;
}

// scalar multiply
// n*P = P + P + P + ... + P
// assume n >= 2
function ECC_GF2m_scalar_mul( n )
{
   // indent one more level
   var save_indent = cur_indent;
   cur_indent += "  ";
   accumulated_output_info += cur_indent + "Scalar Multiply: " + n + "*" + this.format() + "\n";

   if ( this.is_zero() )
   {
      accumulated_output_info += cur_indent + "Returning Zero\n";
      cur_indent = save_indent;
      return this;
   }
   
 
   // use double and add approach
   var res = new ECC_GF2m_Point( 0, 0 );     // start with zero point
   var res_mul=0;                   // res = __ * P
   var P2n = this;                    // copy the starting point
   var P2n_mul = 1;                 // G2n = __ * P
   while( true )
   {
      if ( (n&1) == 1 )             // have a 1 bit here?
      {
         accumulated_output_info += cur_indent + "Calculating " +
                  (res_mul+P2n_mul) + "*" + this.format() + " = " +
                  res_mul + "*" + this.format() + " + " +
                  P2n_mul + "*" + this.format() + " = " +
                  res.format() + " + " + P2n.format() + "\n";
         
         res_mul += P2n_mul;        // update result multiplier
         res = res.add( P2n );            // add the current 2^n * P
         accumulated_output_info += cur_indent + "Working result: " + res_mul +
                     "*" + this.format() + " = " + res.format() + "\n";
      }
      
      if ( n <= 1 )
         break;
      
      // double P
      accumulated_output_info += cur_indent + "Doubling " +
                  P2n_mul + "*" + this.format() + " = " + P2n.format() + "\n";
      P2n = P2n.ECC_GF2m_double();             // get 2^(n+1) P (double it)
      P2n_mul *= 2;                 // update our multiplier
      accumulated_output_info += cur_indent + "Double value: " + P2n_mul + "*" +
                     this.format() + " = " + P2n.format() + "\n";
      
      n = n >> 1;                   // halve n
   }
   
   accumulated_output_info += cur_indent + "Product is " + res.format() + "\n";
   cur_indent = save_indent;
  
   return res;
}

// invert a point (x,-y) mod p
function ECC_GF2m_invert()
{
   if ( this.is_zero() )
      return this;
   
   // negate the y value
   var inverse = new ECC_GF2m_Point( this.x, ECC_GF2m_F.add( this.x, this.y ) );
   accumulated_output_info += cur_indent + "  Inverse of " + this.format() + " is " + inverse.format() + "\n";
 
   return inverse;
}

// format for display
function ECC_GF2m_format()
{
   // do we have the zero point?
   if ( this.is_zero() )
      return "(Zero)";
   
   // not zero, display point
   return "(0x" + this.x.toString(16) + ",0x" + this.y.toString(16) + ")";
}

// create a point on the curve
function ECC_GF2m_Point( x, y )
{
   this.x = x;
   this.y = y;
   this.add = ECC_GF2m_add;
//   this.invert = ECC_GF2m_invert;
   this.smul = ECC_GF2m_scalar_mul;
   this.format = ECC_GF2m_format;
   this.is_zero = ECC_GF2m_is_zero;
   this.invert = ECC_GF2m_invert;
   // put in for subfunction use
   this.ECC_GF2m_double = ECC_GF2m_double;
   this.ECC_GF2m_add_distinct = ECC_GF2m_add_distinct;
}

// base set of values for the ECC curves
// F: underlying field: GF(p) or GF(2^m)
// a, b = coordinates for the curve
//    GF(p):   y^2 = x^3 + ax + b
//    GF(2^m): y^2 + xy = x^3 + ax^2 + b
// G = generator point
// n = order of the point
// h = ratio to # of total points (order)

// sample curves for GF(2^m)
// poly=83 (g^7+g+1), a=1, b=23, G=(0x03,0x6d), n=71, h=2
// poly=83 (g^7+g+1), a=49, b=66, G=(0x01,0x3c), n=73, h=2
// poly=89 (g^7+g^3+1), a=0, b=81, G=(0x02,0x58), n=37, h=4
// poly=89 (g^7+g^3+1), a=15, b=114, G=(0x01,0x24), n=73, h=2 ***
ECC_GF2m_F = new GF2m( 7, 0x89 );
ECC_GF2m_a = 15;
ECC_GF2m_b = 114;
ECC_GF2m_G = new ECC_GF2m_Point( 0x01, 0x24 );
ECC_GF2m_n = 73;
ECC_GF2m_h = 2;

// last part of public key Q=d*G
// private key
ECC_GF2m_d = 7;

// GF(p): 7*(2,9) = (38,63)
// GF(2^m): 7 * (0x01, 0x24) = ???
ECC_GF2m_Q = ECC_GF2m_G.smul( ECC_GF2m_d );

// display the GF(p) curve
function print_ECC_GF2m()
{
   document.write( "Public Key: m=" + ECC_GF2m_F.m );
   document.write( ", generator polynomial=" + GF2m_format_poly(ECC_GF2m_F.poly) );
   document.write( ", a=" + ECC_GF2m_a );
   document.write( ", b=" + ECC_GF2m_b );
   document.write( ", G=" + ECC_GF2m_G.format() );
   document.write( ", Q=" + ECC_GF2m_Q.format() );
   document.write( ", n=" + ECC_GF2m_n );
   document.write( ", h=" + ECC_GF2m_h );
   document.write( "<BR>Private key: d=" + ECC_GF2m_d );
}
//----------------------------------
//  Other useful functions
//----------------------------------

// generate a random integer between 1 and n-1
function gen_rand( n )
{
   return Math.floor( Math.random() * (n-1) ) +1;
}

// get the generator point for the selected curve
function get_G()
{
   // which curve are they using?
   if ( document.ECC.choose_curve[0].checked )
   {
      // using GF(p)
      return ECC_GFp_G;
   }
   else
   {
      // using GF(2^m)
      return ECC_GF2m_G;
   }
}

// get Q, the value of d*G
function get_Q()
{
   // which curve are they using?
   if ( document.ECC.choose_curve[0].checked )
   {
      // using GF(p)
      return ECC_GFp_Q;
   }
   else
   {
      // using GF(2^m)
      return ECC_GF2m_Q;
   }
}

// get the order of the selected curve
function get_n()
{
   // which curve are they using?
   if ( document.ECC.choose_curve[0].checked )
   {
      // using GF(p)
      return ECC_GFp_n;
   }
   else
   {
      // using GF(2^m)
      return ECC_GF2m_n;
   }
}

// get the private value d
function get_d()
{
   // which curve are they using?
   if ( document.ECC.choose_curve[0].checked )
   {
      // using GF(p)
      return ECC_GFp_d;
   }
   else
   {
      // using GF(2^m)
      return ECC_GF2m_d;
   }
}