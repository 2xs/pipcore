# PipInternals

Pip enables the user to create a collection of memory partitions, with a
hierarchical organisation where a parent partition can manage the memory
of its child partitions.

## Memory management :
### The description of all primitives
Pip exports 8 primitives related to memory management:

* `createPartition`: creates a new child partition, given five free pages (which will become Partition Descriptor, Page Directory, Shadow 1, 2 and linked list)
* `deletePartition`: deletes the given child partition
* `addVaddr`: maps a page from the current partition into the given child partition
* `removeVaddr`: gets back a page from a child partition
* `prepare`: prepares a child partition for page map, given the required amount of pages (see pageCount)
* `collect`: retrieves the empty indirection tables, and gives them back to the caller
* `pageCount`: returns the amount of pages required to perform a prepare operation
* `mappedInChild`: checks whether a page has been derivated in a child partition or not

Pip also exports the primitives `dispatch` and `resume` that are discussed below and are related to control flow.

### Data structure 
In order to control, allow or decline memory operations, Pip uses several data structures to keep track of derivations.

#### Partition descriptor
The partition descriptor is the first empty page given to createPartition. It contains the following elements, stored into it as a list:

* VAddr in parent partition and PAddr of Partition Descriptor
* VAddr in parent partition and PAddr of Page Directory
* VAddr in parent partition and PAddr of Shadow 1
* VAddr in parent partition and PAddr of Shadow 2
* VAddr in parent partition and PAddr of Linked list
* PAddr of parent partition

The indexes of the elements into this list are always the same in all partitions.

This data structure is inaccessible by any partition.

    |------------------|
    | @V. P.Descriptor |
    | @P. P.Descriptor |
    | @V. P.Directory  |
    | @P. P.Directory  |
    | @V. Shadow 1     |
    | @P. Shadow 1     |
    | @V. Shadow 2     |
    | @P. Shadow 2     |
    | @V. Linked list  |
    | @P. Linked list  |
    |    Null value    |
    | @P. Parent part. |
    |------------------|

#### MMU tables structure (page directory as root) (to reformulate)
The Page Directory is a data structure commonly used in several architectures, including Intel x86 and ARM.
It provides a simple way to describe a virtual memory environment, by cutting a virtual address into indexes.
Its structure is one of a table, containing entries addressed by their offset.

Therefore, each index will point to an entry in one of those tables. The first index will give an entry into the Page Directory.
This entry contains a physical address, which is a "Page Table". We can then take the second index extracted from the virtual address,
and parse the Page Table to find another entry, and so on. 

Example: On x86 32 bits architectures, we have two levels of indirection, which are Page Directory and Page Table.
The first 10 bits of the virtual address points to an entry in the Page Directory, which is the Page Table address.
The middle 10 bits of the virtual address points to an entry in the Page Table, which is the corresponding physical address.
We can then take the remaining 12 bits of the virtual address, OR them with the found physical address, to get the physical address of the source virtual address.

    |------------------|
    |  PAddr      |Fl. |
    |------------------|      
    |  PAddr      |Fl. |      
    |------------------|
    |       ...        |
    |                  |
    |------------------|

This data structure is inaccessible by any partition.

#### Shadow tables structure (sh1 or sh2 as root)
The Shadow 1 and Shadow 2 data structures are exactly the same as Page Directories, the only difference being the data stored within it.
The Shadow 1 contains some flags related to derivation, such as the is_page_directory() flag, which defines whether a page has become a child partition or not.
The Shadow 2 contains some tracking information, which are the virtual address of a page into the parent partition's context.

Both of these data structures are inaccessible by any partition.

#### The last linked list structure
The configuration tables linked list contains the physical address of every data structure page of the current partition (i.e. page directory, page tables, shadow pages and linked list itself), as well as their virtual address in the parent partition. As those pages aren't even mapped in a partition, but only are in their parent, we can't use Shadow 1 or 2 to this purpose. It is structured as list of <VAddr, PAddr> couples.

    |------------------|
    | First free index |
    | @V. Page Table   |
    | @P. Page Table   |
    | @V. Shadow PT1   |
    | @P. Shadow PT1   |
    |       ...        |
    |  @P. Next page   |
    |------------------|

This data structure is not accessible by any partition.

## Interrupt layer and scheduling
### Functional description
In addition to memory management, we need to allow proper interrupts
multiplexing and dispatching to the right child partition. (`dispatch`)

We also want to provide a way of implementing ~trap calls between parent and
child partitions. (`notify`)

### Design 
In order to keep the Pip kernel as 'exo' as possible, we keep most of the
scheduler out of the kernel. The Pip kernel provides only context saving and
switching primitives. All the complex scheduling logics must be implemented
in userland.

We keep the same hierarchical organisation that was used for the memory. 
Therefore, a parent partition should take care of managing the execution
flow of its children partitions.

#### Pipflags
For now, pipflags holds only the `vcli` flag (bit 0), which enables a partition to mask virtual interrupts, and the `stack fault` flag, which is set when the interrupted stack overflowed.

#### Saved contexts
When an interrupt occurs, the interrupted context can be saved in two different places according to the current state of the partition :
- If the VCLI flag is not set, Pip tries to push the interrupted context info onto the interrupted stack; if the stack overflows, the context is instead pushed onto the VIDT's context buffer, which is located at offset 0xF0C from the beginning of the VIDT, and sets the `stack fault` flag
- If the VCLI flag is set, Pip pushes the interrupted context info onto the VIDT's context buffer.

The interrupted context's stack can be found at entry ESP(0) of the interrupted partition's VIDT, from which the interrupted context info can be found as well.

#### On occurence of an hardware interrupt
- If the interrupt happens in kernel-land, it is ignored
- If the root partition has no handler registered for this interrupt, it is ignored as well
- The current partition's context is saved and interrupted
- The root partition is notified of the signal

#### On occurence of an exception
- Kernel-land exceptions trigger a panic
- If the current partition is the root partition, it is notified to itself
- Else, the target partition is the parent partition
- The interrupted context is saved
- The target partition is notified

#### Context switching
To resume a child context, a pip-service has been added: `resume`
This service allows a parent partition to activate a child partition and 
switch to one of its contexts.
ie. `resume(part_no, 0)` to activate child partition `part_no` and
	resume its interrupted context, resetting or not the VCLI flag.

#### Dispatch
The `dispatch` service allows a partition to dispatch an interrupt to a child partition or to its parent.
This function triggers a partition/context switch. It does not save the caller context, and never returns.
It is mainly meant to forward a hardware interrupt to a child partition (discarding the parent's interrupt
handler context).

PipFlags:

- In the calling partition: If target is a child, `vcli` = 0
- In the target partition:  `vcli` = 1

#### Resume
The `resume` service activates another partition, and restores the execution of the specified saved context.
This function is meant to be called from an interrupt/notify handler, and never returns to the caller.
Arguments are: target partition, and context to resume.

This service is usually used by a parent when implementing the scheduling of its child partitions. 

PipFlags:

- In the calling partition: `vcli` = 0

