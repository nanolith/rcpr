.globl dummytest

#dummytest takes three integer arguments and returns the greatest.
#int dummy(int x, int y, int z)

.text
dummytest:
    mov %rdi, %rax      # set the return value initially to x
    cmp %rsi, %rax      # compare x and y
    cmovl %rsi, %rax    # set the return value to y if x < y
    cmp %rdx, %rax      # compare z and max(x, y)
    cmovl %rdx, %rax    # set the return value to z if it is greater.
    ret
