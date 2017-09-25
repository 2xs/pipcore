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




#ifndef __HPET__
#define __HPET__



//---------------------------------------------------------------------
// HPET support definitions
//---------------------------------------------------------------------
#define hpetUSE_HPET_TIMER_NUMBER			(0 )	  // 0 = false, 1 = true

#define hpetUSE_HPET_TIMER_NUMBER_0			( 1 )	  // 0 = false, 1 = true
#define hpetUSE_HPET_TIMER_NUMBER_1	 		( 1 )	  // 0 = false, 1 = true
#define hpetUSE_HPET_TIMER_NUMBER_2	 		( 1 )	  // 0 = false, 1 = true

//---------------------------------------------------------------------
// HPE timers general purpose register addresses
//---------------------------------------------------------------------
#define hpetHPET_GENERAL_ID					( *( ( volatile uint32_t * ) 0xFED00000UL ) )
#define hpetHPET_COUNTER_TICK_PERIOD		( *( ( volatile uint32_t * ) 0xFED00004UL ) )
#define hpetHPET_GENERAL_CONFIGURATION		( *( ( volatile uint32_t * ) 0xFED00010UL ) )
#define hpetHPET_GENERAL_STATUS				( *( ( volatile uint32_t * ) 0xFED00020UL ) )
#define hpetHPET_MAIN_CTR_LOW		 		( *( ( volatile uint32_t * ) 0xFED000F0UL ) )
#define hpetHPET_MAIN_CTR_HIGH		 		( *( ( volatile uint32_t * ) 0xFED000F4UL ) )

//---------------------------------------------------------------------
// HPE timer specific support definitions
//---------------------------------------------------------------------
#if (hpetUSE_HPET_TIMER_NUMBER_0 == 1)
	#define TIMER0_TRIGGERING 				( 0 )		// 1 = level, 0 = edge
	#define TIMER0_POLARITY 				( 0 )		// 0 = active high, 1 = active low
	#define TIMER0_IRQ						( 2 )		// 0 is default for legacy 8259, 2 for IO APIC
	#define hpetHPET_TIMER0_ISR_VECTOR 		( 0x32 )  	// HPET Timer - I/O APIC
	#define hpetHPET_TIMER0_INTERRUPT_RATE	( 2000 )	// Number of times per second to interrupt
	#define hpetHPET_TMR0_CONFIG_LOW		( *( ( volatile uint32_t * ) 0xFED00100UL ) )
	#define hpetHPET_TMR0_CONFIG_HIGH		( *( ( volatile uint32_t * ) 0xFED00104UL ) )
	#define hpetHPET_TMR0_COMPARATOR_LOW	( *( ( volatile uint32_t * ) 0xFED00108UL ) )
	#define hpetHPET_TMR0_COMPARATOR_HIGH	( *( ( volatile uint32_t * ) 0xFED0010CUL ) )
#endif
#if (hpetUSE_HPET_TIMER_NUMBER_1 == 1)
	#define TIMER1_TRIGGERING 				( 0 )		// 1 = level, 0 = edge
	#define TIMER1_POLARITY 				( 0 )		// 0 = active high, 1 = active low
	#define TIMER1_IRQ						( 8 )		// 8 is default for 8259 & IO APIC
	#define hpetHPET_TIMER1_ISR_VECTOR 		( 0x85 )  	// HPET Timer - I/O APIC
	#define hpetHPET_TIMER1_INTERRUPT_RATE	( 1500 )	// Number of times per second to interrupt
	#define hpetHPET_TMR1_CONFIG_LOW		( *( ( volatile uint32_t * ) 0xFED00120UL ) )
	#define hpetHPET_TMR1_CONFIG_HIGH		( *( ( volatile uint32_t * ) 0xFED00124UL ) )
	#define hpetHPET_TMR1_COMPARATOR_LOW	( *( ( volatile uint32_t * ) 0xFED00128UL ) )
	#define hpetHPET_TMR1_COMPARATOR_HIGH	( *( ( volatile uint32_t * ) 0xFED0012CUL ) )
#endif
#if (hpetUSE_HPET_TIMER_NUMBER_2 == 1)
	#define TIMER2_TRIGGERING 				( 0 )		// 1 = level, 0 = edge
	#define TIMER2_POLARITY 				( 0 )		// 0 = active high, 1 = active low
	#define TIMER2_IRQ						( 11 )		// 11 is default for 8259 & IO APIC
	#define hpetHPET_TIMER2_ISR_VECTOR 		( 0x95 )  	// HPET Timer - I/O APIC
	#define hpetHPET_TIMER2_INTERRUPT_RATE	( 1400 )	// Number of times per second to interrupt
	#define hpetHPET_TMR2_CONFIG_LOW		( *( ( volatile uint32_t * ) 0xFED00140UL ) )
	#define hpetHPET_TMR2_CONFIG_HIGH		( *( ( volatile uint32_t * ) 0xFED00144UL ) )
	#define hpetHPET_TMR2_COMPARATOR_LOW	( *( ( volatile uint32_t * ) 0xFED00148UL ) )
	#define hpetHPET_TMR2_COMPARATOR_HIGH	( *( ( volatile uint32_t * ) 0xFED0014CUL ) )
#endif

//---------------------------------------------------------------------
// Disables code if no timer is enabled (quiets the compiler)
//---------------------------------------------------------------------
#define hpetHPET_TIMER_IN_USE (hpetUSE_HPET_TIMER_NUMBER_0 | hpetUSE_HPET_TIMER_NUMBER_1 | hpetUSE_HPET_TIMER_NUMBER_2)

//---------------------------------------------------------------------
// Allow HPET variable printout on screen (1 = allow)
//---------------------------------------------------------------------
#define hpetHPET_PRINT_INFO 				0

//---------------------------------------------------------------------
// HPET bit checking and manipulation definitions
//---------------------------------------------------------------------
#define hpetHPET_CFG_ENABLE 				0x001
#define hpetHPET_CFG_LEGACY 				0x002
#define hpetHPET_TN_ENABLE          		0x004
#define hpetHPET_TN_PERIODIC        		0x008
#define hpetHPET_TN_PERIODIC_CAP    		0x010
#define hpetHPET_TN_SETVAL          		0x040
#define hpetHPET_TN_32BIT           		0x100
#define hpetHPET_INT_EDGE 					0x000
#define hpetHPET_INT_LEVEL 					0x001
#define hpetHPET_POL_HIGH 					0x000
#define hpetHPET_POL_LOW 					0x001

//---------------------------------------------------------------------
// I/O APIC register addresses and definitions
//---------------------------------------------------------------------
#define hpetIO_APIC_IDX						( *( ( volatile uint32_t * ) 0xFEC00000UL ) )
#define hpetIO_APIC_WDW						( *( ( volatile uint32_t * ) 0xFEC00010UL ) )
#define hpetIO_APIC_EOI						( *( ( volatile uint32_t * ) 0xFEC00040UL ) )

#define hpetIO_APIC_ID						0x00	// Get/Set APIC ID information
#define hpetIO_APIC_VERSION					0x01	// Get APIC version information
#define hpetIO_APIC_RTE_OFFSET				0x10 	// add 2* RTE Table (0-23) to this offset

//---------------------------------------------------------------------
// Used for timer calibration
//---------------------------------------------------------------------
#define hpetLVTIMER 						( 0 )	 // Constant definition
#define hpetHPETIMER 						( 1 )	 // Constant definition

//---------------------------------------------------------------------
// HPET variables Structure
//---------------------------------------------------------------------
struct __attribute__ ((__packed__)) hpet_info
{
	unsigned int	timer_number;
	unsigned int	main_counter_h;
	unsigned int	main_counter_l;
	unsigned int	comparator_h;
	unsigned int	comparator_l;
	unsigned int    total_interrupts;
	unsigned int	elapsed_seconds;
};

//---------------------------------------------------------------------
// Variables other modules may want to access
//---------------------------------------------------------------------
extern volatile uint32_t hpet_general_status;
extern volatile uint32_t ulHPETtimerNumber [3];
extern volatile uint32_t ulHPETTotalInterrupts [3];
extern volatile uint32_t ulHPETElapsedSeconds [3];
extern volatile uint32_t ulHPETInterruptFrequency [3];
extern volatile uint32_t ulHPETTicksToInterrupt [3];
extern struct hpet_info PrintInfo[3];

//---------------------------------------------------------------------
// Function prototypes
//---------------------------------------------------------------------
#if (hpetHPET_TIMER_IN_USE)
	void vClearHPETElapsedSeconds( void );
	uint32_t uiCalibrateTimer(uint32_t timerNumber, uint32_t TimerType );
	void vInitializeAllHPETInterrupts( void );
	void vCreateHPETInfoUpdateTask( void  );
#endif



void initHPETInterrupts();

void initilizeHPETInterrupt(uint32_t timerNumber);

void vStopHPETTimer( uint32_t ClearCounters );
void vClearHPETCounters( void );


void vSetupIOApic( uint32_t timerNumber );
uint32_t uiCalibrateHPETTimer(uint32_t timerNumber, uint32_t Calibrate);

void vCheckHPETIRQCapabilities( uint32_t timerNumber);


void vGetHPETCapabilitiesAndStatus( void );

void vSetHPETComparator( uint32_t timerNumber, uint64_t Value );

void vConfigureHPETTimer( uint32_t timerNumber, uint32_t PeriodicMode  );

void vStartHPETTimer( void );


void vSetTVS( uint32_t timerNumber );

void vHPETIRQHandler0( void );
void vHPETIRQHandler1( void );
void vHPETIRQHandler2( void );



void vHPET_ISR( uint32_t TimerNumber );


uint64_t ullReadHPETCounters( void );


uint64_t ullReadHPETCounters( void );

uint32_t uiCalibrateTimer( uint32_t TimerNumber, uint32_t TimerType);

#endif
