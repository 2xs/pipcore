#include <stdint.h>
#include <pip/fpinfo.h>
#include <pip/debug.h>

void main(pip_fpinfo* bootinfo)
{
    Pip_Debug_Puts("Hello world!\n");
    for(;;);
}  
