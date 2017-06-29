/*
 * Copyright (C) 2015, Intel Corporation. All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * 3. Neither the name of the copyright holder nor the names of its
 *    contributors may be used to endorse or promote products derived
 *    from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * ``AS IS'' AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
 * FOR A PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE
 * COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
 * (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
 * STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
 * ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED
 * OF THE POSSIBILITY OF SUCH DAMAGE.
 */

#ifndef CPU_X86_DRIVERS_QUARKX1000_ETH_H_
#define CPU_X86_DRIVERS_QUARKX1000_ETH_H_

#include <stdint.h>
#include "helpers.h"
#include "pci.h"

#define IP_BUFSIZE 1280
#define MIN_PAGE_SIZE_SHAMT 12
#define MIN_PAGE_SIZE (1 << MIN_PAGE_SIZE_SHAMT)
static uint32_t ip_len = IP_BUFSIZE;

typedef union {
    uint32_t u32[(IP_BUFSIZE + 3) / 4];
    uint8_t u8[IP_BUFSIZE];
} ip_buf_t;

static ip_buf_t ip_aligned_buffer;

#define ip_buf (ip_aligned_buffer.u8)



/** \brief 16 bit 802.15.4 address */
typedef struct ip_802154_shortaddr {
    uint8_t addr[2];
} ip_802154_shortaddr;
/** \brief 64 bit 802.15.4 address */
typedef struct ip_802154_longaddr {
    uint8_t addr[8];
} ip_802154_longaddr;

/** \brief 802.11 address */
typedef struct ip_80211_addr {
    uint8_t addr[6];
} ip_80211_addr;

/** \brief 802.3 address */
typedef struct ip_eth_addr {
    uint8_t addr[6];
} ip_eth_addr;



typedef pci_driver_t quarkX1000_eth_driver_t;

/* Refer to Intel Quark SoC X1000 Datasheet, Chapter 15 for more details on
 * Ethernet device operation.
 *
 * This driver puts the Ethernet device into a very simple and space-efficient
 * mode of operation.  It only allocates a single packet descriptor for each of
 * the transmit and receive directions, computes checksums on the CPU, and
 * enables store-and-forward mode for both transmit and receive directions.
 */

/* Transmit descriptor */
typedef struct quarkX1000_eth_tx_desc {
    /* First word of transmit descriptor */
    union {
        struct {
            /* Only valid in half-duplex mode. */
            uint32_t deferred_bit      : 1;
            uint32_t err_underflow     : 1;
            uint32_t err_excess_defer  : 1;
            uint32_t coll_cnt_slot_num : 4;
            uint32_t vlan_frm          : 1;
            uint32_t err_excess_coll   : 1;
            uint32_t err_late_coll     : 1;
            uint32_t err_no_carrier    : 1;
            uint32_t err_carrier_loss  : 1;
            uint32_t err_ip_payload    : 1;
            uint32_t err_frm_flushed   : 1;
            uint32_t err_jabber_tout   : 1;
            /* OR of all other error bits. */
            uint32_t err_summary       : 1;
            uint32_t err_ip_hdr        : 1;
            uint32_t tx_timestamp_stat : 1;
            uint32_t vlan_ins_ctrl     : 2;
            uint32_t addr2_chained     : 1;
            uint32_t tx_end_of_ring    : 1;
            uint32_t chksum_ins_ctrl   : 2;
            uint32_t replace_crc       : 1;
            uint32_t tx_timestamp_en   : 1;
            uint32_t dis_pad           : 1;
            uint32_t dis_crc           : 1;
            uint32_t first_seg_in_frm  : 1;
            uint32_t last_seg_in_frm   : 1;
            uint32_t intr_on_complete  : 1;
            /* When set, descriptor is owned by DMA. */
            uint32_t own               : 1;
        };
        uint32_t tdes0;
    };
    /* Second word of transmit descriptor */
    union {
        struct {
            uint32_t tx_buf1_sz        : 13;
uint32_t                   : 3;
                             uint32_t tx_buf2_sz        : 13;
                             uint32_t src_addr_ins_ctrl : 3;
        };
        uint32_t tdes1;
    };
    /* Pointer to frame data buffer */
    uint8_t *buf1_ptr;
    /* Unused, since this driver initializes only a single descriptor for each
     * direction.
     */
    uint8_t *buf2_ptr;
} quarkX1000_eth_tx_desc_t;

/* Transmit descriptor */
typedef struct quarkX1000_eth_rx_desc {
    /* First word of receive descriptor */
    union {
        struct {
            uint32_t ext_stat          : 1;
            uint32_t err_crc           : 1;
            uint32_t err_dribble_bit   : 1;
            uint32_t err_rx_mii        : 1;
            uint32_t err_rx_wdt        : 1;
            uint32_t frm_type          : 1;
            uint32_t err_late_coll     : 1;
            uint32_t giant_frm         : 1;
            uint32_t last_desc         : 1;
            uint32_t first_desc        : 1;
            uint32_t vlan_tag          : 1;
            uint32_t err_overflow      : 1;
            uint32_t length_err        : 1;
            uint32_t s_addr_filt_fail  : 1;
            uint32_t err_desc          : 1;
            uint32_t err_summary       : 1;
            uint32_t frm_len           : 14;
            uint32_t d_addr_filt_fail  : 1;
            uint32_t own               : 1;
        };
        uint32_t rdes0;
    };
    /* Second word of receive descriptor */
    union {
        struct {
            uint32_t rx_buf1_sz        : 13;
            uint32_t                   : 1;
                             uint32_t addr2_chained     : 1;
                             uint32_t rx_end_of_ring    : 1;
                             uint32_t rx_buf2_sz        : 13;
            uint32_t                   : 2;
                             uint32_t dis_int_compl     : 1;
        };
        uint32_t rdes1;
    };
    /* Pointer to frame data buffer */
    uint8_t *buf1_ptr;
    /* Unused, since this driver initializes only a single descriptor for each
     * direction.
     */
    uint8_t *buf2_ptr;
} quarkX1000_eth_rx_desc_t;

/* Driver metadata associated with each Ethernet device */
typedef struct quarkX1000_eth_meta {
    /* Transmit descriptor */
    volatile quarkX1000_eth_tx_desc_t tx_desc;
    /* Transmit DMA packet buffer */
    volatile uint8_t tx_buf[ALIGN(IP_BUFSIZE, 4)];
    /* Receive descriptor */
    volatile quarkX1000_eth_rx_desc_t rx_desc;
    /* Receive DMA packet buffer */
    volatile uint8_t rx_buf[ALIGN(IP_BUFSIZE, 4)];

#if X86_CONF_PROT_DOMAINS == X86_CONF_PROT_DOMAINS__PAGING
    /* Domain-defined metadata must fill an even number of pages, since that is
     * the minimum granularity of access control supported by paging.  However,
     * using the "aligned(4096)" attribute causes the alignment of the kernel
     * data section to increase, which causes problems when generating UEFI
     * binaries, as is described in the linker script.  Thus, it is necessary
     * to manually pad the structure to fill a page.  This only works if the
     * sizes of the actual fields of the structure are collectively less than a
     * page.
     */
    uint8_t pad[MIN_PAGE_SIZE -
        (sizeof(quarkX1000_eth_tx_desc_t) +
         ALIGN(IP_BUFSIZE, 4) +
         sizeof(quarkX1000_eth_rx_desc_t) +
         ALIGN(IP_BUFSIZE, 4))];
#endif
} __attribute__((packed)) quarkX1000_eth_meta_t;

#define LOG_PFX "quarkX1000_eth: "

#define MMIO_SZ 0x2000

#define MAC_CONF_14_RMII_100M          BIT(14)
#define MAC_CONF_11_DUPLEX             BIT(11)
#define MAC_CONF_3_TX_EN               BIT(3)
#define MAC_CONF_2_RX_EN               BIT(2)

#define OP_MODE_25_RX_STORE_N_FORWARD  BIT(25)
#define OP_MODE_21_TX_STORE_N_FORWARD  BIT(21)
#define OP_MODE_13_START_TX            BIT(13)
#define OP_MODE_1_START_RX             BIT(1)

#define INT_ENABLE_NORMAL              BIT(16)
#define INT_ENABLE_RX                  BIT(6)

#define REG_ADDR_MAC_CONF              0x0000
#define REG_ADDR_MACADDR_HI            0x0040
#define REG_ADDR_MACADDR_LO            0x0044
#define REG_ADDR_TX_POLL_DEMAND        0x1004
#define REG_ADDR_RX_POLL_DEMAND        0x1008
#define REG_ADDR_RX_DESC_LIST          0x100C
#define REG_ADDR_TX_DESC_LIST          0x1010
#define REG_ADDR_DMA_OPERATION         0x1018
#define REG_ADDR_INT_ENABLE            0x101C

void quarkX1000_eth_setup(uintptr_t meta_phys_base);


void quarkX1000_eth_init(void);
void quarkX1000_eth_poll(uint16_t *frame_len);
void quarkX1000_eth_send(void);
void send(uint8_t * buf, int len);
void poll(uint8_t * buf, uint32_t loop_score);

#endif /* CPU_X86_DRIVERS_QUARKX1000_ETH_H_ */
