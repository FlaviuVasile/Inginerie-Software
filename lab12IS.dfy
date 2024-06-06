/*method Triple (x: int ) returns (r: int)
 {
 var y := 2 * x;
 r := x + y;
 assert r==3*x;
 }
*/

/*method Triple (x: int ) returns (r: int)
{
 var y := 2 * x;
 r := x + y;
 assert r == 10 * x;
 assert r < 5;
 assert false ;
 } */ //nu merge 

 /*method Triple (x: int ) returns (r: int)
 {
 if x == 0{
 r := 0;
 } else {
 var y := 2 * x;
 r := x + y;
 }
 assert r == 3 * x;
 }*/

 /*method Triple (x: int ) returns (r: int)
 {
 if {
 case x < 18 =>
 var a, b := 2 * x, 4 * x;
 r := (a+b) / 2;
 case 0 <= x =>
 var y := 2 * x;
 r := x + y;
 }
 assert r == 3 * x;
 }
 method Triple (x: int) returns (r: int)
{
    var y := 2 * x;
    r := x + y;
    assert r == 3 * x;
    assert r >= 0;  
}

/* method Caller ()
{
var result := Triple (18) ;
assert result < 100;
}
/*method Triple (x: int ) returns (r: int)
ensures r == 3 * x
{
var y := 2 * x;
r := x + y;
}*/
method Triple (x: int ) returns (r: int)
requires x % 2 == 0
ensures r == 3 * x
{
var y := x / 2;
r := 6 * y;
 }
 */

*/

/*>function sum2(n:nat):nat
{
    n*(n+1)/2
}
method Sum(n: nat) returns (sum: nat)
    requires n >= 0
    ensures sum >= 0
    ensures sum==sum2(n)
{
    var s := 0;
    var i := 0;
    while i <= n
        invariant 0 <= i <= n + 1
        invariant s == i * (i - 1) / 2
        invariant s >= 0
    {
        s := s + i;
        i := i + 1;
    }
    sum := s;
}
