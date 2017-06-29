#include <string.h>
#include <assert.h>
#include <stdio.h>
#include <pip/io.h>
#include "eth.h"
#include "pci.h"
#include "helpers.h"
#include "debug.h"
#include "galileo-support.h"
static quarkX1000_eth_driver_t drv;


static pci_config_addr_t pci_addr = {.raw = 0};
static uint32_t bar0;
static uint32_t mmio;
static uint32_t mmio_size;
static uint32_t mac_config_reg;
static ip_eth_addr mac_addr;
static struct quarkX1000_eth_tx_desc tx_desc;
static struct quarkX1000_eth_rx_desc rx_desc;
static quarkX1000_eth_meta_t meta;

static uint32_t sizeBuffer = ALIGN(IP_BUFSIZE,4);
static uint8_t tx_buf[ALIGN(IP_BUFSIZE,4)];
static uint8_t rx_buf[ALIGN(IP_BUFSIZE,4)];


/**
 * \fn void getPciInfo (pci_config_addr_t pci_addr)
 * \brief Get Ethernet PCI information
 *
 * \param pci_config_addr_t pci interface
 *
 */

void getPciInfo(pci_config_addr_t pci_addr){

    pci_addr.reg_off = 0x0000;
    uint16_t vendor = pci_config_read(pci_addr);
    DEBUG(INFO,"Vendor : %x",vendor);
    pci_addr.reg_off = 0x0002;
    uint16_t id = pci_config_read(pci_addr);
    DEBUG(INFO,"ID : %x",id);

}
void pciCommandBitsEnable(pci_config_addr_t pci_addr){

    pci_addr.reg_off = 0x4;

    uint16_t command_reg = pci_config_read(pci_addr);

    pci_addr.reg_off = 0x4;

    command_reg = command_reg | BIT(2) | BIT(1);
    pci_config_write(pci_addr,command_reg);
    pci_addr.reg_off = 0x4;
}


void initPciDevice(pci_config_addr_t pci_addr){

    mmio_size = 0x2000;

    mmio = pci_config_read(pci_addr) & ~0xFFF;
    DEBUG(TRACE,"MMIO ADDRESS : %x",mmio);

    mac_config_reg = mmioRead(mmio,0x0,4);

    DEBUG(TRACE,"MAC Configuration Register : %x",mac_config_reg);
}




/* Initialize transmit descriptor. */
void initTransmitDesc(pci_config_addr_t pci){

    DEBUG(TRACE,"Initialize and install the transmit descriptor\n");
    tx_desc.tdes0 = 0;
    tx_desc.tdes1 = 0;

    tx_desc.buf1_ptr = (uint8_t *)tx_buf;
    tx_desc.tx_end_of_ring = 1;
    tx_desc.first_seg_in_frm = 1;
    tx_desc.last_seg_in_frm = 1;
    tx_desc.tx_end_of_ring = 1;


    DEBUG(TRACE,"Saving the strcture used to receive the sending packet")
    mem_write(mmio,REG_ADDR_TX_DESC_LIST,4,(uint32_t)&tx_desc);
    DEBUG(TRACE,"Transmit descriptor installed\n");

}


/* Initialize receive descriptor. */
void initReceiveDesc(pci_config_addr_t pci){
    DEBUG(TRACE,"Initialize and install the receive descriptor\n");

    rx_desc.rdes0 = 0;
    rx_desc.rdes1 = 0;

    rx_desc.buf1_ptr = (uint8_t *)rx_buf;
    rx_desc.own = 1;
    rx_desc.first_desc = 1;
    rx_desc.last_desc = 1;
    rx_desc.rx_buf1_sz = IP_BUFSIZE;
    rx_desc.rx_end_of_ring = 1;

    DEBUG(TRACE,"Saving the strcture used to receive the sending packet")
    mem_write(mmio,REG_ADDR_RX_DESC_LIST,4,(uint32_t)&rx_desc);
    DEBUG(TRACE,"Receive descriptor installed\n");


}





void ethPoll(pci_config_addr_t pci,uint32_t * frame_len){
    uint16_t frm_len;
    DEBUG(TRACE,"Check whether the RX descriptor is still owned by the device, if not an error occured");

    if(rx_desc.own == 0){

        if(rx_desc.err_summary == 0){
            DEBUG(ERROR,"ERROR receiving frame: RDES0 = %08x, RDES1 = %08x.\n",rx_desc.rdes0, rx_desc.rdes1);
            for(;;);
        }
        frm_len = rx_desc.frm_len;

        if(frm_len > IP_BUFSIZE){
            DEBUG(ERROR,"ERROR length of the packet is too long");
            for(;;);
        }

        MEMCPY_TO_META(ip_buf,(void *)rx_buf,frm_len);

        rx_desc.own = 1;

        DEBUG(TRACE,"Getting back the packet");
        mem_write(mmio,REG_ADDR_RX_POLL_DEMAND,4,1);


    }else{
        DEBUG(TRACE,"Spurious recieve interrupt from Ethernet MAC");
    }
}
void poll(uint8_t * buf, uint32_t loop_score){
    ethPoll(pci_addr,&ip_len);
    MEMCPY_TO_META(buf,ip_buf,IP_BUFSIZE);


}

void ethSend(pci_config_addr_t pci){

    DEBUG(TRACE,"Wait until the tx descriptor is no longer owned by the device\n");
    while(tx_desc.own == 1);

    DEBUG(TRACE,"Check whether an error occured transmitting the previous frame\n");
    if(tx_desc.err_summary) {
        DEBUG(ERROR,"Error transmitting frame: TDES0 = %08x, TDES1 = %08x.\n",tx_desc.tdes0, tx_desc.tdes1);
        for(;;);
    }

    DEBUG(TRACE,"Start transmitting the packet !");


    MEMCPY_TO_META((void *)tx_buf,ip_buf,IP_BUFSIZE);
    int i;

    for(i= 0;i<IP_BUFSIZE;i++)
        if(ip_buf[i] != tx_buf[i])
            DEBUG(ERROR,"BUFFER INCORRECT");

    tx_desc.tx_buf1_sz = IP_BUFSIZE;
    tx_desc.own = 1;

    mem_write(mmio,REG_ADDR_TX_POLL_DEMAND,4,1);

    DEBUG(TRACE,"Packet transmitted");
}

void send(uint8_t * buf, int len){
    if(len > IP_BUFSIZE)
        DEBUG(ERROR,"ETHERNET : Send buffer length is too long");

    MEMCPY_TO_META(ip_buf,buf,len);

    ethSend(pci_addr);

    uint32_t debugReg = mmioRead(mmio,0x24,4);
    DEBUG(TRACE,"DEBUG REG : %x\r",debugReg);
 }


/*---------------------------------------------------------------------------*/
/**
 * \brief Initialize the first Quark X1000 Ethernet MAC.
 *
 *        This procedure assumes that an MMIO range for the device was
 *        previously assigned, e.g. by firmware.
 */
    void
quarkX1000_eth_init(void)
{
    pci_addr.dev = 20;
    pci_addr.func = 6;


    getPciInfo(pci_addr);
    pciCommandBitsEnable(pci_addr);


    uint32_t mac1,mac2;


    uint32_t i;
    for(i=0;i<IP_BUFSIZE;i++)
        rx_buf[i] = tx_buf[i] = 0;


    pci_addr.reg_off = PCI_CONFIG_REG_BAR0;

    initPciDevice(pci_addr);

    mac1 = mmioRead(mmio,0x0040,4);
    mac2 = mmioRead(mmio,0x0044,4);


    mac_addr.addr[5] = (uint8_t)(mac1 >> 8);
    mac_addr.addr[4] = (uint8_t)mac1;
    mac_addr.addr[3] = (uint8_t)(mac2 >> 24);
    mac_addr.addr[2] = (uint8_t)(mac2 >> 16);
    mac_addr.addr[1] = (uint8_t)(mac2 >> 8);
    mac_addr.addr[0] = (uint8_t)mac2;


    DEBUG(INFO,"MAC address = %02x:%02x:%02x:%02x:%02x:%02x.\n",
            mac_addr.addr[0],
            mac_addr.addr[1],
            mac_addr.addr[2],
            mac_addr.addr[3],
            mac_addr.addr[4],
            mac_addr.addr[5]
         );


    initTransmitDesc(pci_addr);
    initReceiveDesc(pci_addr);

    uint32_t confReg = mem_read(mmio,REG_ADDR_MAC_CONF,4);
    confReg |= MAC_CONF_14_RMII_100M;
    confReg |= MAC_CONF_11_DUPLEX;
    confReg |= MAC_CONF_3_TX_EN;
    confReg |= MAC_CONF_2_RX_EN;

    mem_write(mmio, REG_ADDR_MAC_CONF, 4, confReg );


	/* Mask all the MMC interrupts */



	mem_write(mmio, REG_ADDR_INT_ENABLE, 4,
		  INT_ENABLE_NORMAL |
		  /* Enable receive interrupts */
		  INT_ENABLE_RX);


    mem_write(mmio, REG_ADDR_DMA_OPERATION, 4,
            /* Enable receive store-and-forward mode for simplicity. */
            OP_MODE_25_RX_STORE_N_FORWARD |
            /* Enable transmit store-and-forward mode for simplicity. */
           OP_MODE_21_TX_STORE_N_FORWARD |
            /* Place the transmitter state machine in the Running
               state. */
            OP_MODE_13_START_TX |
            /* Place the receiver state machine in the Running state. */
            OP_MODE_1_START_RX);

    DEBUG(TRACE,"Enabled 100M Full-duplex mode\n");
}
/*---------------------------------------------------------------------------*/
