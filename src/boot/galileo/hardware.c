/*******************************************************************************/
/*  © Université Lille 1, The Pip Development Team (2015-2016)                 */
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

/**
 * \file mmu.c
 * \brief MMU early-boot configuration
 */
#include <stdint.h>
#include "debug.h"
#include <libc.h>
#include "galileo-support.h"
#include "GPIO_I2C.h"
#include "HPET.h"
#include "portmacro.h"
#include "hardware.h"



void setupHardware()
{
    if(PIP_DEBUG_MODE)
        initGalileoSerialPort(DEBUG_SERIAL_PORT);
    DEBUG(INFO, "-> Initializing SERIAL PORT.\n");
    initGalileoGPIO();
    DEBUG(INFO,"-> Initializing GPIO.\n");
    vGalileoInitializeLegacyGPIO();
    DEBUG(INFO,"-> Initializing Legacy GPIO.\n");

#if(hpetUSE_HPET_TIMER_NUMBER)
    {
        __asm volatile("cli");
        initHPETInterrupts();
        DEBUG(INFO,"-> Initializing HPET Interrupts\n");
    }
#endif
    DEBUG(INFO,"-> Calibrate Timer\n");
    calibrateLVTimer();
}





void calibrateLVTimer( void )
{
uint32_t uiInitialTimerCounts, uiCalibratedTimerCounts;

	/* Disable LAPIC Counter. */
	portAPIC_LVT_TIMER = portAPIC_DISABLE;

	/* Calibrate the LV Timer counts to ensure it matches the HPET timer over
	extended periods. */
	uiInitialTimerCounts = ( ( configCPU_CLOCK_HZ >> 4UL ) / configTICK_RATE_HZ );
	uiCalibratedTimerCounts = uiCalibrateTimer( 0, hpetLVTIMER );

	if( uiCalibratedTimerCounts != 0 )
	{
		uiInitialTimerCounts = uiCalibratedTimerCounts;
	}

	/* Set the interrupt frequency. */
	portAPIC_TMRDIV = portAPIC_DIV_16;
	portAPIC_TIMER_INITIAL_COUNT = uiInitialTimerCounts;

	/* Enable LAPIC Counter. */
	portAPIC_LVT_TIMER = portAPIC_TIMER_PERIODIC | portAPIC_TIMER_INT_VECTOR;

	/* Sometimes needed. */
	portAPIC_TMRDIV = portAPIC_DIV_16;
}



