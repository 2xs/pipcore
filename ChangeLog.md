# Version 0.2 - TBD
## Changes

- Reworked the x86 IAL to ensure proper management of interrupt routing. 
	- The dispatch and resume pipcalls now behave like the INT and IRET instructions, allowing proper communication between partitions.
	- The VIDT now contains only an emergency interrupt context buffer, and context resume information are now pushed onto the interrupted stack to allow interrupt handlers to get the appropriate information easily.
	- System boot now enables both PGE and PCIDE if they are supported, according to the values returned by CPUID.

- Fixed various bugs in the x86 bootstrap sequence.
	- Fixed a problem where the MMU translation tables were still visible and accessible from the root partition.

- Improved the x86 bootstrap sequence.
	- The memory map given to the root partition is now a flat, linear memory space no matter how the initial physical memory map is structured.
	- Inaccessible device memory ranges, such as the VGA controller memory space, can now be remapped to another address on boot.

- Fixed various bugs in the x86 MAL.
	- Fixed a vulnerability where various system calls may fail in legitimate cases, due to an invalid virtual memory read.
	- Integrated process context identifiers in CR3 management, allowing it to be used on a future x64 port.

- Added pipcalls.
	- The "mappedInChild" call was added, allowing a partition to know if a page has been derivated into a child partition or not.
	- Missing callgate entries were added.

- Proof work-in-progress.
	- The "createPartition" service is now fully proved.
	- The "addVaddr" service is now fully proved.

- Port integration
    - The first version of Intel Galileo Gen. 2 port is now available.

# Version 0.1 - 03/10/2016

- Initial release of the Pip proto-kernel.
