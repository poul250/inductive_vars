export function w $bar() {
@start
      %i =w copy 10
      %s =w copy 0
      %c =w copy 1
@loop
      %x =w add 1, 2
      %s =w add %s, %i
      %i =w sub %i, %c
      jnz %i, @loop, @end
@end
      ret %s
}