Pip enables the user to create a collection of memory partitions, with a
hierarchical organisation where a parent partition can manage the memory
of its child partitions.

## Memory management :
### The description of all primitives
Pip exports 7 primitives related to memory management :

* createPartition : creates a new child partition, given five free pages (which will become Partition Descriptor, Page Directory, Shadow 1, 2 and linked list)
* deletePartition : deletes the given child partition
* addVaddr : maps a page from the current partition into the given child partition
* removeVaddr : gets back a page from a child partition
* prepare : prepares a child partition for page map, given the required amount of pages (see pageCount)
* collect : retrieves the empty indirection tables, and gives them back to the caller
* pageCount : returns the amount of pages required to perform a prepare operation

### Data structure 
In order to control, allow or decline memory operations, Pip uses several data structures to keep track of derivations.

#### Partition descriptor
The partition descriptor is the first empty page given to createPartition. It contains the following elements, stored into it as a list :

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
For now, pipflags holds only the `vcli` flag (bit 0), which enables a partition to mask virtual interrupts.

#### Saved contexts
To enable the creation of userland schedulers, the Pip kernel needs to save the execution contexts in several places:

- occurence of an hardware interrupt
- occurence of an exception
- on a call to notify

Saved context for x86 architecture:

	00:	eip		Instruction pointer
	04:	pipflags	Saved pip flags
	08:	eflags		Saved eflags
	0C:	registers	8 general purpose registers
	2C:	valid		Indicates context presence
	30:	nfu		Padding
	40:

The contexts are saved in the partition's vidt.
There are 4 contexts slots in the vidt.

	0: INT_CTX: 		The partition was interrupted
	1: ISR_CTX: 		The partition triggered a fault
	2: NOTIF_CHILD_CTX:  	The partition called notify on a child
	3: NOTIF_PARENT_CTX:  	The partition called notify on its parent

When saving a context, pip sets the `valid` flag to indicate 
the presence of a valid context.

If a partition needs to implement some complex scheduling, ie. for the 
implementation of inter-process-communication, it should take care of 
saving/resuming the contexts of its children. (The parent can always access
its child vidt thanks to vertical sharing).

#### On occurence of an hardware interrupt
- If kernelland, return
- if root partition don't handle the interruption (vcli is set, or no handler is registered):
    return
- Save context of current partition (`INT_CTX`)
- Dispatch interruption to the root partition

#### On occurence of an exception
- If kernelland: panic
- If current partition is root: `dest` = root partition
- Else: `dest` = parent of current_partition
- Save context of current partition (`ISR_CTX`)
- If exception is not handled by `dest`:  yield root partition
- Else: dispatch exception to `dest`

#### Context switching
To resume a child context, a pip-service has been added: `resume`
This service allows a parent partition to activate a child partition and 
switch to one of its contexts.
ie. `resume(part_no, INT_CTX)` to activate child partition `part_no` and
	resume its interrupted context.

When a context is resumed, its `valid` flag is zeroed.

The resume service also allows a child partition to resume its parent's
`NOTIF_CHILD_CTX` at the end of a notify handler.
This is the current `viret` implementation.

If the `NOTIF_CHILD_CTX` of the parent is not valid, pip will yield the root
partition instead (by dispatching vint 0 on root partition).

### Saved contexts usage
#### `INT_CTX` & `ISR_CTX`
While a partition is executing, the first two contexts (`INT_CTX` and `ISR_CTX`)
might be written by the kernel at any time. (For example when hardware interruptions occurs.)

Hence it can not be manipulated atomically by the partition itself. Only the
parent of a partition can manipulate these two.

(An exception exists for the root partition which has no parent and must handle
these two contexts itself. It's possible there because the root partition can
globally mask interrupts when `vcli` flag is set in its PipFlags)

When a fault is triggered by a partition (P2), it is dispatched to it's parent (P1).
P1 exception handler should look like:

	- Identify the faulty child using the `caller` argument of the interrupt handler
	Either:
	- Read/fix ISR_CTX in child's vidt.
	- Resume(child, ISR_CTX)
	Or:
 	- Stop/delete partition

If no exception handler was present in P1, P1 can still detect the fault before
resuming P2, by checking the `valid` flag of child's `ISR_CTX`.

#### `NOTIF_PARENT_CTX`
The `NOTIF_PARENT_CTX` is saved when a partition call `notify` on its parent.
It is to be resumed by the parent at end of its notify handler.
Typically, the notify handler of the parent should just end with a
`resume(caller, NOTIF_PARENT_CTX)` to continue execution of the child. 

#### `NOTIF_CHILD_CTX`
The `NOTIF_CHILD_CTX` is saved when a partition call `notify` on one of its children.
This context is to be manipulated by the partition itself and should be handled with great care.

Indeed, as said in the 'Context switching' part, a child is allowed to trigger a switch to 
this context by calling `viret`. 

Therefore, before activating a child partition, the parent must always ensure that its own `NOTIF_CHILD_CTX`
is either invalid, or corresponds to the child partition that is beeing activated. 
Otherwise, a child partition could call `resume(0, NOTIF_CHILD_CTX)` and restore a `NOTIF_CHILD_CTX` that was 
meant to another child partition.

#### Dispatch
The `dispatch` service allows a partition to dispatch an interrupt to a child partition or to its parent.
This function triggers a partition/context switch. It does not save the caller context, and never returns.
It is mainly meant to forward a hardware interrupt to a child partition (discarding the parent's interrupt
handler context).

PipFlags:

- In the calling partition: If target is a child, `vcli` = 0
- In the target partition:  `vcli` = 1

#### Notify
The `notify` service allows a partition to trigger an interrupt in a child partition or in its parent.
It is similar to the `dispatch` and rely on the same kernel primitives, but provides a different behavior.
Unlike `dispatch`, this function triggers a context saving in the caller (`NOTIF_CHILD_CTX`/`NOTIF_PARENT_CTX`),
and should return to the caller after it has been handled by the callee. 

PipFlags: 

- In the calling partition: If target is a child, `vcli` = 0;
- In the target partition:  `vcli` = 1

#### Resume
The `resume` service activates another partition, and restores the execution of the specified saved context.
This function is meant to be called from an interrupt/notify handler, and never returns to the caller.
Arguments are: target partition, and context to resume.

This service is usually used by a parent when implementing the scheduling of its child partitions. 
When called by a child on its parent, only the `NOTIF_CHILD_CTX` context is allowed.

PipFlags:

- In the calling partition: `vcli` = 0

