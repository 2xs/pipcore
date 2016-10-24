#include <stdint.h>
#include <pip/fpinfo.h>
#include <pip/debug.h>
#include <pip/api.h>
#include <pip/vidt.h>
void main(pip_fpinfo* bootinfo)
{
    vsti();
    notify(0,66);
    //puts("Hello world!\n");
    for(;;);
}
