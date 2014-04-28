// Variable shadow in method defintion.

int main () {
  Counter c;
  c = new Counter;
  c.incr(1);
  c.incr(20);
  c.incr(100);
  int x = c.value();
  printInt(x);
  return 0;
}

class Counter {
  int val;

  void incr (int val) {val = val; return;}

  int value () {return val;}

}
