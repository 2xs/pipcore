#include <stdint.h>
#include <pip/fpinfo.h>
#include <pip/api.h>
//#include <pip/debug.h>
#include <pip/vidt.h>
#include "eth.h"
#include "debug.h"
#include "galileo-support.h"


INTERRUPT_HANDLER(asmInterrupt33,interrupt33)
    vcli();
    printf("MULTIPLEXER GOT INTERRUPT 33\n");
    vsti();
    viret();
    END_OF_INTERRUPT
INTERRUPT_HANDLER(asmInterrupt40,interrupt40)
    vcli();
    printf("MULTIPLEXER GOT INTERRUPT 40\n");
    vsti();
    viret();

    END_OF_INTERRUPT
INTERRUPT_HANDLER(asmInterrupt44,interrupt44)

    END_OF_INTERRUPT


INTERRUPT_HANDLER(asmInterrupt14,interrupt14)
    vcli();
    for(;;);
    END_OF_INTERRUPT

INTERRUPT_HANDLER(asmInterrupt15,interrupt15)
    vcli();
    for(;;);
    END_OF_INTERRUPT


void printPacket (void * buffer) {
    unsigned int size = IP_BUFSIZE;
    printf("\n***********\nNew Packet holding %d bytes of data %p\n***********\n", size, buffer);
    char *c;
    int counter=0;
    int i;
    for (i=2; i<size+2; i++) {
        c = (char *)buffer+i;
        if ( *c != '\0' ) {
            printf("%2x ", *c);
            counter++;
        }
        else {
            return;
        }
    }
}


uint8_t packet[68] = {  0x55,0x55,0x55,0x55,0x55,0x55,0x55,0xD5,0xff,0xff,0xff,0xff,0xff,0xff,0x98,0x4f,
                        0xee,0x05,0x64,0x32,0x08,0x06,0x00,0x01,0x08,0x00,0x06,0x04,0x00,0x01,0x98,0x4f,
                        0xee,0x05,0x64,0x32,0xC0,0xa8,0x00,0x0b,0x00,0x00,0x00,0x00,0x00,0x00,0xC0,0xa8,
                        0x00,0x0a,0x06,0x01,0x04,0x00,0x00,0x00,0x00,0x02,0x01,0x00,0x03,0x02,0x00,0x00,
                        0x05,0x01,0x03,0x01};



uint8_t rpacket[IP_BUFSIZE];
void main(pip_fpinfo* bootinfo)
{
    initGalileoSerialPort(DEBUG_SERIAL_PORT);

    registerInterrupt(33, &interrupt33, (uint32_t*)0x1000000);
    registerInterrupt(40, &interrupt40, (uint32_t*)0x2000000);
    registerInterrupt(14, &interrupt14, (uint32_t*)0x3000000);
    registerInterrupt(15, &interrupt15, (uint32_t*)0x4000000);

    //vsti();
    printf("HELLO FROM USERLAND\n");
    quarkX1000_eth_init();
    uint32_t time = pip_time();
    DEBUG(TRACE,"TIME : %d\n",time);
    send(packet,68);
    for(;;);
        //printf("Time : %d\n",pip_time());


}
