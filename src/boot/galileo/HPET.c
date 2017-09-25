/*******************************************************************************/
/*  © Université Lille 1, The Pip Development Team (2015-2017)                 */
/*                                                                             */
/*  This software is a computer program whose purpose is to run a minimal,     */
/*  hypervisor relying on proven properties such as memory isolation.          */
/*                                                                             */
/*  This software is governed by the CeCILL license under French law and       */
/*  abiding by the rules of distribution of free software.  You can  use,      */
/*  modify and/ or redistribute the software under the terms of the CeCILL     */
/*  license as circulated by CEA, CNRS and INRIA at the following URL          */
/*  "http://www.cecill.info".                                                  */
/*                                                                             */
/*  As a counterpart to the access to the source code and  rights to copy,     */
/*  modify and redistribute granted by the license, users are provided only    */
/*  with a limited warranty  and the software's author,  the holder of the     */
/*  economic rights,  and the successive licensors  have only  limited         */
/*  liability.                                                                 */
/*                                                                             */
/*  In this respect, the user's attention is drawn to the risks associated     */
/*  with loading,  using,  modifying and/or developing or reproducing the      */
/*  software by the user in light of its specific status of free software,     */
/*  that may mean  that it is complicated to manipulate,  and  that  also      */
/*  therefore means  that it is reserved for developers  and  experienced      */
/*  professionals having in-depth computer knowledge. Users are therefore      */
/*  encouraged to load and test the software's suitability as regards their    */
/*  requirements in conditions enabling the security of their systems and/or   */
/*  data to be ensured and,  more generally, to use and operate it in the      */
/*  same conditions as regards security.                                       */
/*                                                                             */
/*  The fact that you are presently reading this means that you have had       */
/*  knowledge of the CeCILL license and that you accept its terms.             */
/*******************************************************************************/



#include "galileo-support.h"
#include "HPET.h"
#include "portmacro.h"
#include <stdint.h>



uint32_t hpet_general_id;
uint32_t hpet_counter_tick_period;

void initHPETInterrupts()
{
#if( hpetUSE_HPET_TIMER_NUMBER_0 )
    initilizeHPETInterrupt( 0 );
#endif
#if( hpetUSE_HPET_TIMER_NUMBER_1 )
    initilizeHPETInterrupt( 1 );
#endif
#if( hpetUSE_HPET_TIMER_NUMBER_2 )
    initilizeHPETInterrupt( 2 );
#endif
}

/*-----------------------------------------------------------------------
 * Global variables
 *------------------------------------------------------------------------
 */
volatile uint32_t hpet_general_status;
volatile uint32_t ulHPETTimerNumber [3] = {0, 1, 2};
volatile uint32_t ulHPETTotalInterrupts [3] = {0, 0, 0};
volatile uint32_t ulHPETElapsedSeconds [3] = {0, 0, 0};
volatile uint32_t ulHPETInterruptFrequency [3] = {0, 0, 0};
volatile uint32_t ulHPETTicksToInterrupt [3] = {0, 0, 0};

void initilizeHPETInterrupt(uint32_t timerNumber)
{

    /* NOTE: In non-legacy mode interrupts are sent as MSI messages to LAPIC */

    uint32_t ticks_per_ms = 0UL;			// Get # ticks per ms
    uint32_t InterruptFrequency = 0UL;		// Get times per second to interrupt

    /* Stop the timers and reset the main counter */
    vStopHPETTimer(true);

    /* Initialise hardware */
    vSetupIOApic(timerNumber);

    /* Register ISRs.  Purely for demonstration purposes, timer 0 and timer 2
       use the central interrupt entry code, so are installed using
       xPortRegisterCInterruptHandler(), while timer 1 uses its own interrupt
       entry code, so is installed using xPortInstallInterruptHandler().  For
       convenience the entry code for timer 1 is implemented at the bottom of
       RegTest.S.See
http://www.freertos.org/RTOS_Intel_Quark_Galileo_GCC.html#interrupts for
more information. */
#if( hpetUSE_HPET_TIMER_NUMBER_0 == 1 )
    {
        if (timerNumber == 0)
        {
            InterruptFrequency = hpetHPET_TIMER0_INTERRUPT_RATE;
            xPortRegisterCInterruptHandler( vHPETIRQHandler0, hpetHPET_TIMER0_ISR_VECTOR );
        }
    }
#endif
#if( hpetUSE_HPET_TIMER_NUMBER_1 == 1 )
    {
        if (timerNumber == 1)
        {
            extern void vApplicationHPETTimer1Wrapper( void );

            InterruptFrequency = hpetHPET_TIMER1_INTERRUPT_RATE;
            xPortInstallInterruptHandler( vHPETIRQHandler1, hpetHPET_TIMER1_ISR_VECTOR );
        }
    }
#endif
#if ( hpetUSE_HPET_TIMER_NUMBER_2 == 1)
    {
        if (timerNumber == 2)
        {
            InterruptFrequency = hpetHPET_TIMER2_INTERRUPT_RATE;
            xPortRegisterCInterruptHandler( vHPETIRQHandler2, hpetHPET_TIMER2_ISR_VECTOR );
        }
    }
#endif

    /* Get calibrated ticks per millisecond before initialization. */
    ticks_per_ms = uiCalibrateHPETTimer(timerNumber, TRUE);

    /* Check IRQ compatibility - will assert here if there is a problem. */
    vCheckHPETIRQCapabilities(timerNumber);

    /* Get HPET capabilities and ID and status */
    vGetHPETCapabilitiesAndStatus();

    /* Sanity check for frequency */
    if ( InterruptFrequency < 1 )
        InterruptFrequency = 20;	// default is 50 ms interrupt rate

    /* Save interrupt frequency */
    ulHPETInterruptFrequency[timerNumber] = InterruptFrequency;

    /* Calculate required number of ticks */
    uint32_t ticks = ( ticks_per_ms * 1000UL ) / ulHPETInterruptFrequency[timerNumber];

    /* Save the number of ticks to interrupt */
    ulHPETTicksToInterrupt[timerNumber] = ticks;

    /* Make sure counters are zeroed */
    vClearHPETCounters();

    /* Write out comparator value */
    vSetHPETComparator(timerNumber, ticks);

    /* Set target timer non-periodic mode with first interrupt at tick */
    vConfigureHPETTimer(timerNumber, FALSE);

    /* Start the timer */
    vStartHPETTimer();


}


void vStopHPETTimer( uint32_t ClearCounters )
{
    uint32_t hpet_cfg = 0UL;

    /* Clear configuration enable bit */
    hpet_cfg = hpetHPET_GENERAL_CONFIGURATION;
    hpet_cfg &= ~hpetHPET_CFG_ENABLE;
    hpetHPET_GENERAL_CONFIGURATION = hpet_cfg;

    /* Clear counters */
    if (ClearCounters)
        vClearHPETCounters();
}



void vClearHPETCounters( void )
{
    hpetHPET_MAIN_CTR_LOW = 0UL;
    hpetHPET_MAIN_CTR_HIGH = 0UL;
}

void vSetupIOApic( uint32_t timerNumber )
{
    uint8_t DeliveryMode = 1; 					// 0 means fixed (use ISR Vector)
    uint8_t DestinationMode = 0;  				// Used by local APIC for MSI
    uint8_t IRQPolarity = 1;					// 0 means active high, 1 = active low
    uint8_t InterruptMask = 0;					// 0 means allow interrupts
    uint8_t Triggering = hpetHPET_INT_EDGE;		// Level or Edge sensitive
    uint8_t IRQNumber = 0;						// Hardware IRQ number
    uint8_t ISRVector = 0;						// Desired ISR vector

    /* Select polarity and triggering */
#if( hpetUSE_HPET_TIMER_NUMBER_0 == 1 )
    {
        if (timerNumber == 0)
        {
            IRQNumber = TIMER0_IRQ;
            ISRVector = hpetHPET_TIMER0_ISR_VECTOR;
            IRQPolarity = TIMER0_POLARITY;
            Triggering = TIMER0_TRIGGERING;
        }
    }
#endif
#if( hpetUSE_HPET_TIMER_NUMBER_1 == 1 )
    {
        if (timerNumber == 1)
        {
            IRQNumber = TIMER1_IRQ;
            ISRVector = hpetHPET_TIMER1_ISR_VECTOR;
            IRQPolarity = TIMER1_POLARITY;
            Triggering = TIMER1_TRIGGERING;
        }
    }
#endif
#if( hpetUSE_HPET_TIMER_NUMBER_2 == 1 )
    {
        if (timerNumber == 2)
        {
            IRQNumber = TIMER2_IRQ;
            ISRVector = hpetHPET_TIMER2_ISR_VECTOR;
            IRQPolarity = TIMER2_POLARITY;
            Triggering = TIMER2_TRIGGERING;
        }
    }
#endif

    /* Data to write to RTE register Lower DW */
    uint32_t ConfigDataLDW = (uint32_t)(ISRVector | ((DeliveryMode & 0x07) << 8UL));

    /* Set or clear bits in configuration data */
    if (DestinationMode == 0)
        ConfigDataLDW &= ~(1UL << 11UL);
    else
        ConfigDataLDW |= (1UL << 11UL);

    if (IRQPolarity == 0)
        ConfigDataLDW &= ~(1UL << 13UL);
    else
        ConfigDataLDW |= (1UL << 13UL);

    if (Triggering != FALSE)
        ConfigDataLDW |= (1UL << 15UL);
    else
        ConfigDataLDW &= ~(1UL << 15UL);

    if (InterruptMask == 0)
        ConfigDataLDW &= ~(1UL << 16UL);
    else
        ConfigDataLDW |= (1UL << 16UL);

    /* Data to write to RTE register Upper DW */
    uint32_t LocalAPIC_DID = ((portAPIC_ID_REGISTER & 0xFF000000UL) >> 24UL); 	// get local APIC DID
    uint32_t LocalAPIC_EDID = ((portAPIC_ID_REGISTER & 0x00FF0000UL) >> 16UL);	// get local APIC Extended DID
    uint32_t ConfigDataUDW = (uint32_t)(((LocalAPIC_DID << 24UL) & 0xFF000000UL) |
            ((LocalAPIC_EDID << 16UL) & 0x00FF0000UL));

    /* Setup IDX and WDW register to write RTE data */
    hpetIO_APIC_IDX = hpetIO_APIC_RTE_OFFSET + ((2 * IRQNumber) + 1);
    hpetIO_APIC_WDW = ConfigDataUDW;
    hpetIO_APIC_IDX = hpetIO_APIC_RTE_OFFSET + ((2 * IRQNumber) + 0);
    hpetIO_APIC_WDW = ConfigDataLDW;
}





uint32_t uiCalibrateHPETTimer(uint32_t timerNumber, uint32_t Calibrate)
{
    uint32_t ticks_per_ms = 15422; // 1e-3/64.84127e-9 (denominator is hpet_counter_tick_period)
    if (Calibrate)
    {
        uint32_t uiRunningTotal = 0UL;
        uint32_t i = 0UL;
        for (i = 0; i < 5; i++)
            uiRunningTotal += uiCalibrateTimer(timerNumber, hpetHPETIMER);
        ticks_per_ms = (uiRunningTotal / 5);
    }
    return ticks_per_ms;
}




void vCheckHPETIRQCapabilities( uint32_t timerNumber)
{
    uint32_t hpet_cfg_h = 0UL;
    uint32_t hpet_cfg_l = 0UL;
    uint32_t IRQNumber = 0UL;
    uint32_t Triggering = hpetHPET_INT_EDGE;

#if( hpetUSE_HPET_TIMER_NUMBER_0 == 1 )
    {
        if (timerNumber == 0)
        {
            IRQNumber = TIMER0_IRQ;
            Triggering = TIMER0_TRIGGERING;
            hpet_cfg_h = hpetHPET_TMR0_CONFIG_HIGH;
            hpet_cfg_l = hpetHPET_TMR0_CONFIG_LOW;
        }
    }
#endif
#if( hpetUSE_HPET_TIMER_NUMBER_1 == 1 )
    {
        if (timerNumber == 1)
        {
            IRQNumber = TIMER1_IRQ;
            Triggering = TIMER1_TRIGGERING;
            hpet_cfg_h = hpetHPET_TMR1_CONFIG_HIGH;
            hpet_cfg_l = hpetHPET_TMR1_CONFIG_LOW;
        }
    }
#endif
#if( hpetUSE_HPET_TIMER_NUMBER_2 == 1 )
    {
        if (timerNumber == 2)
        {
            IRQNumber = TIMER2_IRQ;
            Triggering = TIMER2_TRIGGERING;
            hpet_cfg_h = hpetHPET_TMR2_CONFIG_HIGH;
            hpet_cfg_l = hpetHPET_TMR2_CONFIG_LOW;
        }
    }
#endif

    /* Setup configuration register */
    hpet_cfg_l |= hpetHPET_TN_ENABLE | hpetHPET_TN_PERIODIC |
        hpetHPET_TN_32BIT | ((IRQNumber & 0x1F) << 9UL);

    /* Setup triggering bit */
    if (Triggering != hpetHPET_INT_EDGE)
        hpet_cfg_l |= (1UL << 1UL);
    else
        hpet_cfg_l &= ~(1UL << 1UL);

    /* Write then read back configuration */
#if( hpetUSE_HPET_TIMER_NUMBER_0 == 1 )
    {
        if (timerNumber == 0)
        {
            hpetHPET_TMR0_CONFIG_HIGH = hpet_cfg_h;
            hpetHPET_TMR0_CONFIG_LOW = hpet_cfg_l;
            hpet_cfg_l = hpetHPET_TMR0_CONFIG_LOW;
        }
    }
#endif
#if( hpetUSE_HPET_TIMER_NUMBER_1 == 1 )
    {
        if (timerNumber == 1)
        {
            hpetHPET_TMR1_CONFIG_HIGH = hpet_cfg_h;
            hpetHPET_TMR1_CONFIG_LOW = hpet_cfg_l;
            hpet_cfg_l = hpetHPET_TMR1_CONFIG_LOW;
        }
    }
#endif
#if( hpetUSE_HPET_TIMER_NUMBER_2 == 1 )
    {
        if (timerNumber == 2)
        {
            hpetHPET_TMR2_CONFIG_HIGH = hpet_cfg_h;
            hpetHPET_TMR2_CONFIG_LOW = hpet_cfg_l;
            hpet_cfg_l = hpetHPET_TMR2_CONFIG_LOW;
        }
    }
#endif
}





void vGetHPETCapabilitiesAndStatus( void )
{
    /* Get HPET capabilities and ID */
    hpet_general_id = hpetHPET_GENERAL_ID;

    /* Invalid vendor ID - Should be Intel (0x8086") */
    if ((hpet_general_id >> 16) != 0x8086UL)
    {
        for(;;);
    }

    /* Get number of ns/tick - default is 69.841279 */
    hpet_counter_tick_period = hpetHPET_COUNTER_TICK_PERIOD;

    /* General status of HPET -  bit 0 = T0, bit 1 = T1 and bit 2 = T2.
     * In level triggered mode 1 means interrupt is active */
    hpet_general_status = hpetHPET_GENERAL_STATUS;
}



void vSetHPETComparator( uint32_t timerNumber, uint64_t Value )
{
#if( hpetUSE_HPET_TIMER_NUMBER_0 == 1 )
    {
        if (timerNumber == 0)
        {
            vSetTVS(timerNumber);
            hpetHPET_TMR0_COMPARATOR_LOW = (uint32_t)(Value & 0xFFFFFFFFULL);
            vSetTVS(timerNumber);
            hpetHPET_TMR0_COMPARATOR_HIGH = (uint32_t)((Value >> 32UL) & 0xFFFFFFFFULL);
        }
    }
#endif
#if( hpetUSE_HPET_TIMER_NUMBER_1 == 1 )
    {
        if (timerNumber == 1)
        {
            vSetTVS(timerNumber);
            hpetHPET_TMR1_COMPARATOR_LOW = (uint32_t)(Value & 0xFFFFFFFFULL);
            vSetTVS(timerNumber);
            hpetHPET_TMR1_COMPARATOR_HIGH = (uint32_t)((Value >> 32UL) & 0xFFFFFFFFULL);
        }
    }
#endif
#if( hpetUSE_HPET_TIMER_NUMBER_2 == 1 )
    {
        if (timerNumber == 2)
        {
            vSetTVS(timerNumber);
            hpetHPET_TMR2_COMPARATOR_LOW = (uint32_t)(Value & 0xFFFFFFFFULL);
            vSetTVS(timerNumber);
            hpetHPET_TMR2_COMPARATOR_HIGH = (uint32_t)((Value >> 32UL) & 0xFFFFFFFFULL);
        }
    }
#endif
}





void vConfigureHPETTimer( uint32_t timerNumber, uint32_t PeriodicMode  )
{
    uint32_t hpet_cfg = 0UL;				// Configuration data
    uint8_t  IRQNumber = 0;					// Hardware ISR number
    uint8_t  Triggering = 0;				// Level or Edge sensitive

#if( hpetUSE_HPET_TIMER_NUMBER_0 == 1 )
    {
        if (timerNumber == 0)
        {
            IRQNumber = TIMER0_IRQ;
            Triggering = TIMER0_TRIGGERING;
            hpet_cfg = hpetHPET_TMR0_CONFIG_LOW;
        }
    }
#endif
#if( hpetUSE_HPET_TIMER_NUMBER_1 == 1 )
    {
        if (timerNumber == 1)
        {
            IRQNumber = TIMER1_IRQ;
            Triggering = TIMER1_TRIGGERING;
            hpet_cfg = hpetHPET_TMR1_CONFIG_LOW;
        }
    }
#endif
#if( hpetUSE_HPET_TIMER_NUMBER_2 == 1 )
    {
        if (timerNumber == 2)
        {
            IRQNumber = TIMER2_IRQ;
            Triggering = TIMER2_TRIGGERING;
            hpet_cfg = hpetHPET_TMR2_CONFIG_LOW;
        }
    }
#endif

    /* Modify configuration */
    if (PeriodicMode != FALSE)
    {
        hpet_cfg |= hpetHPET_TN_ENABLE | hpetHPET_TN_PERIODIC | hpetHPET_TN_SETVAL |
            hpetHPET_TN_32BIT | ((IRQNumber & 0x1F) << 9UL);
    }
    else
    {
        hpet_cfg |= hpetHPET_TN_ENABLE | hpetHPET_TN_SETVAL |
            hpetHPET_TN_32BIT | ((IRQNumber & 0x1F) << 9UL);
    }

    /* Setup triggering bit */
    if (Triggering != hpetHPET_INT_EDGE)
        hpet_cfg |= (1UL << 1UL);
    else
        hpet_cfg &= ~(1UL << 1UL);

    /* write-out configuration */
#if( hpetUSE_HPET_TIMER_NUMBER_0 == 1 )
    if (timerNumber == 0)
    {
        hpetHPET_TMR0_CONFIG_LOW = hpet_cfg;
    }
#endif
#if( hpetUSE_HPET_TIMER_NUMBER_1 == 1 )
    if (timerNumber == 1)
    {
        hpetHPET_TMR1_CONFIG_LOW = hpet_cfg;
    }
#endif
#if( hpetUSE_HPET_TIMER_NUMBER_2 == 1 )
    if (timerNumber == 2)
    {
        hpetHPET_TMR2_CONFIG_LOW = hpet_cfg;
    }
#endif
}



void vStartHPETTimer( void )
{
    uint32_t hpet_cfg = 0UL;
    uint8_t  LegacyMode = TRUE; // See table in doc # 329676 page 867

    hpet_general_status = hpetHPET_GENERAL_STATUS;

    if (hpet_general_status != 0x0UL)
        hpetHPET_GENERAL_STATUS = hpet_general_status;

    hpet_cfg = hpetHPET_GENERAL_CONFIGURATION;
    hpet_cfg |= hpetHPET_CFG_ENABLE;

    if(LegacyMode != FALSE)
        hpet_cfg |= hpetHPET_CFG_LEGACY;
    else
        hpet_cfg &= ~hpetHPET_CFG_LEGACY;

    hpetHPET_GENERAL_CONFIGURATION = hpet_cfg;
}


void vSetTVS( uint32_t timerNumber )
{
    volatile uint32_t hpet_cfg = 0UL;
    const uint32_t uiTVS = (1UL << 6UL);

#if( hpetUSE_HPET_TIMER_NUMBER_0 == 1 )
    {
        if (timerNumber == 0)
        {
            hpet_cfg = hpetHPET_TMR0_CONFIG_LOW | uiTVS;
            hpetHPET_TMR0_CONFIG_LOW = hpet_cfg;
        }
    }
#endif
#if( hpetUSE_HPET_TIMER_NUMBER_1 == 1 )
    {
        if (timerNumber == 1)
        {
            hpet_cfg = hpetHPET_TMR1_CONFIG_LOW | uiTVS;
            hpetHPET_TMR1_CONFIG_LOW = hpet_cfg;
        }
    }
#endif
#if( hpetUSE_HPET_TIMER_NUMBER_2 == 1 )
    {
        if (timerNumber == 2)
        {
            hpet_cfg = hpetHPET_TMR2_CONFIG_LOW | uiTVS;
            hpetHPET_TMR2_CONFIG_LOW = hpet_cfg;
        }
    }
#endif
}




void vHPETIRQHandler0( void )
{
    vHPET_ISR( 0 );
    hpetIO_APIC_EOI = hpetHPET_TIMER0_ISR_VECTOR;
}



void vHPETIRQHandler1( void )
{
    vHPET_ISR( 1 );
    hpetIO_APIC_EOI = hpetHPET_TIMER1_ISR_VECTOR;
}


void vHPETIRQHandler2( void )
{
    vHPET_ISR( 2 );
    hpetIO_APIC_EOI = hpetHPET_TIMER2_ISR_VECTOR;
}


void vHPET_ISR( uint32_t TimerNumber )
{
    /*-----------------------------------------------------------------*/
    /* Notes: In edge triggered mode, no need to clear int status bits.*/
    /*                                                                 */
    /* In non-periodic mode, comparator is added to current counts,    */
    /* do not clear main counters.                                     */
    /*-----------------------------------------------------------------*/
    __asm volatile( "cli" );

    /* Bump HPE timer interrupt count - available in a global variable */
    ulHPETTotalInterrupts[TimerNumber] += 1UL;

    /* Bump HPE timer elapsed seconds count - available in a global variable */
    if ((ulHPETTotalInterrupts[TimerNumber] %
                (ulHPETInterruptFrequency[TimerNumber] + 0UL)) == 0UL)
        ulHPETElapsedSeconds[TimerNumber] += 1UL;

    /* Reload comparators - a must do in non-periodic mode */
    uint64_t ullNewValue = (uint64_t)
        (ullReadHPETCounters() + (uint64_t)ulHPETTicksToInterrupt[TimerNumber]);
    vSetHPETComparator(TimerNumber, ullNewValue);

    __asm volatile( "sti" );
}



uint64_t ullReadHPETCounters( void )
{
    volatile uint64_t Counters = (uint64_t)
        (((uint64_t)hpetHPET_MAIN_CTR_HIGH << 32UL) |
         (uint64_t)hpetHPET_MAIN_CTR_LOW);
    return Counters;
}



uint32_t uiCalibrateTimer( uint32_t TimerNumber, uint32_t TimerType)
{
	/*---------------------------------------------------------------------*/
	/* NOTE: If TimerType = LVTIMER then TimerNumber is ignored (PIT # 2   */
	/* is always used)                                                     */
	/*---------------------------------------------------------------------*/
	/*---------------------------------------------------------------------*/
	/* PIT (programmable interval timer) mode register Bit definitions     */
	/*----------------------------------------------------------------------
	 Mode register is at address 0x43:
	 Bits         Usage
	 6 and 7      Select channel :
	                 0 0 = Channel 0
	                 0 1 = Channel 1
	                 1 0 = Channel 2
	                 1 1 = Read-back command (8254 only)
	 4 and 5      Access mode :
	                 0 0 = Latch count value command
	                 0 1 = Access mode: lobyte only
	                 1 0 = Access mode: hibyte only
	                 1 1 = Access mode: lobyte/hibyte
	 1 to 3       Operating mode :
	                 0 0 0 = Mode 0 (interrupt on terminal count)
	                 0 0 1 = Mode 1 (hardware re-triggerable one-shot)
	                 0 1 0 = Mode 2 (rate generator)
	                 0 1 1 = Mode 3 (square wave generator)
	                 1 0 0 = Mode 4 (software triggered strobe)
	                 1 0 1 = Mode 5 (hardware triggered strobe)
	                 1 1 0 = Mode 2 (rate generator, same as 010b)
	                 1 1 1 = Mode 3 (square wave generator, same as 011b)
	 0            BCD/Binary mode: 0 = 16-bit binary, 1 = four-digit BCD
	----------------------------------------------------------------------*/

	/* Used to calculate LVT ticks */
	const uint32_t uiLargeNumber = 0x7fffffffUL;

	/* Default return value */
	uint32_t ticks = 0;

	/* Check timer type */
	switch (TimerType)
	{
		case hpetLVTIMER:
		case hpetHPETIMER:
			break;
		default:
			return ticks;
			break;
	}

	/* Set timeout counter to a very large value */
	uint64_t timeout_counter = (uint64_t) (uiLargeNumber * 4);

	/* Set PIT Ch2 to one-shot mode */
	uint32_t gate_register = ((inw(GATE_CONTROL) & 0xfd) | 0x01);
	outw(GATE_CONTROL, gate_register);
	outw(MODE_REGISTER, ONESHOT_MODE);

	/* Set counter for 10 ms - 1193180/100 Hz ~ 11932 */
	uint16_t pit_counter = 11932;
	outb(CHANNEL2_DATA, (char) (pit_counter & 0xff));
	outb(CHANNEL2_DATA, (char) ((pit_counter >> 8) & 0xff));

	/* Start target timer  */
	if (TimerType == hpetLVTIMER)
	{
		portAPIC_LVT_TIMER = portAPIC_TIMER_INT_VECTOR;
		portAPIC_TMRDIV = portAPIC_DIV_16;
	}
	else if (TimerType == hpetHPETIMER)
	{
		#if (hpetHPET_TIMER_IN_USE)
			// Initialize HPE timer
			vStopHPETTimer(TRUE);
			/* Write out comparator value - we don't want it to interrupt */
			vSetHPETComparator(TimerNumber, 0xFFFFFFFFUL);
			// Configure HPE timer for non-periodic mode
			vConfigureHPETTimer(TimerNumber, FALSE);
		#else
			( void ) TimerNumber;
		#endif
	}

	/* Reset PIT one-shot counter */
	gate_register = (inw(GATE_CONTROL) & 0xfe);
	outw(GATE_CONTROL, gate_register);
	gate_register |= 0x01;
	outw(GATE_CONTROL, gate_register);

	/* Setup target timer initial counts */
	if (TimerType == hpetLVTIMER)
	{
		portAPIC_TIMER_INITIAL_COUNT = uiLargeNumber;
	}
	else if (TimerType == hpetHPETIMER)
	{
		#if (hpetHPET_TIMER_IN_USE)
			vStartHPETTimer();
		#endif
	}

	/* Wait for PIT counter to expire */
	for (;;)
	{
		gate_register = inw(GATE_CONTROL);
		if ((gate_register & 0x20) || (--timeout_counter == 0))
		{
			/* Stop target timer and exit loop */
			if (TimerType == hpetLVTIMER)
			{
				portAPIC_LVT_TIMER = portAPIC_DISABLE;
				break;
			}
			else if (TimerType == hpetHPETIMER)
			{
				#if (hpetHPET_TIMER_IN_USE)
					vStopHPETTimer(FALSE);
					break;
				#endif
			}
		}
	}

	/* Check for timeout */
	if (timeout_counter != 0)
	{
		if (TimerType == hpetLVTIMER)
		{
			/* Counter started at a large number so subtract counts */
			ticks = (uiLargeNumber - portAPIC_TIMER_CURRENT_COUNT);
			/* adjust ticks for 1 ms and divider ratio */
			ticks = ((((ticks << 4UL) * 100) / 1000) >> 4UL);
		}
		else if (TimerType == hpetHPETIMER)
		{
			#if (hpetHPET_TIMER_IN_USE)
				/* Read timer counter - we only need the low counter */
				ticks = (uint32_t)(ullReadHPETCounters() & 0xFFFFFFFFULL);
				/* Clear timer counter */
				vClearHPETCounters();
				/* Return 1 ms tick counts. Timed for 10 ms so just divide by 10 */
				ticks /= 10;
			#endif
		}
	}

	/* Return adjusted counts for a 1 ms interrupt rate.
	 * Should be approximately 25000 for LV Timer.
	 * Should be approximately 15000 for HPE Timers */
	return ticks;
}
