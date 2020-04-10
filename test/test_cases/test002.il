export function w $is_prime() {
@start
      %n =w copy 17
      %i =w copy 2
@loop
      %m =w rem %n, %i
      jnz %m, @loop2, @end
@loop2
      %i =w add %i, 1
      %t =w ceqw %i, %n
      jnz %t, @end, @loop
@end
      %r =w cnew %m, 0
      ret %r
}