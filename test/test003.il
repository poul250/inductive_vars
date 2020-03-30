#int has_primes(int a, int b) {
#  int mod = 1;
#  for (int i = 0; i < b-a; ++i) {
#    int n = a + i;
#
#    for (int j = 0; j < n-2; ++j) {
#      int divisor = j + 2;
#      mod = n % divisor;
#      if (mod == 0) {
#        break;
#      }
#    }
#    if (mod != 0) {
#      return 1;
#    }
#  }
#
#  return 0;
#}

export function w $has_primes(w %a, w %b) {
@start
    %mod = w copy 1
    %i = w copy 0
@loop1
    %diff = w sub %b, %a
    %cmp = w csltw %i, %diff
    jnz %cmp, @loop1body, @end
@loop1body
    %n = w add %i, %a
    %j = w copy 0
@loop2
    %diff2 = w sub %n, 2
    %cmp2 = w csltw %j, %diff2
    jnz %cmp, @loop2body, @L2
@loop2body
    %divisor = w add %j, 2
    %mod = w rem %n, %divisor
    jnz %mod, @L1, @L2
@L1
    %j = w add %j, 1
    jmp @loop2
@L2
    jnz %mod, @end, @L3
@L3
    %i = w add %i, 1
    jmp @loop1
@end
    %r =w cnew %mod, 0
    ret %r
}