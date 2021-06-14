# PipInternals

Pip enables the user to create a collection of memory partitions, with a
hierarchical organisation where a parent partition can manage the memory
of its child partitions.

## Memory management:

### The description of all primitives

Pip exports 8 primitives related to memory management:

* `createPartition`: creates a new child partition, given five free pages (which
  will become Partition Descriptor, Page Directory, Shadow 1, 2 and linked
  list)
* `countToMap`: returns the amount of pages required to perform a prepare
  operation
* `prepare`: prepares a child partition for page map, given the required amount
  of pages (see `countToMap`)
* `addVAddr`: maps a page from the current partition into the given child
  partition
* `removeVAddr`: gets back a page from a child partition
* `mappedInChild`: checks whether a page has been derivated in a child partition
  or not
* `deletePartition`: deletes the given child partition
* `collect`: retrieves the empty indirection tables, and gives them back to the
  caller

Pip also exports the primitive `yield` that is discussed below and is related
to control flow.

### Data structure

In order to control, allow or decline memory operations, Pip uses several data
structures to keep track of derivations.

#### Partition descriptor

The partition descriptor is the first empty page given to createPartition. It
contains the following elements, stored into it as a list:

* VAddr in parent partition and PAddr of Partition Descriptor
* VAddr in parent partition and PAddr of Page Directory
* VAddr in parent partition and PAddr of Shadow 1
* VAddr in parent partition and PAddr of Shadow 2
* VAddr in parent partition and PAddr of Linked list
* PAddr of parent partition

The indexes of the elements into this list are always the same in all
partitions.

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

The Page Directory is a data structure commonly used in several architectures,
including Intel x86 and ARM. It provides a simple way to describe a virtual
memory environment, by cutting a virtual address into indexes. Its structure is
one of a table, containing entries addressed by their offset.

Therefore, each index will point to an entry in one of those tables. The first
index will give an entry into the Page Directory. This entry contains a physical
address, which is a "Page Table". We can then take the second index extracted
from the virtual address, and parse the Page Table to find another entry, and so
on.

Example: On x86 32 bits architectures, we have two levels of indirection, which
are Page Directory and Page Table. The first 10 bits of the virtual address
points to an entry in the Page Directory, which is the Page Table address. The
middle 10 bits of the virtual address points to an entry in the Page Table,
which is the corresponding physical address. We can then take the remaining 12
bits of the virtual address, OR them with the found physical address, to get the
physical address of the source virtual address.

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

The Shadow 1 and Shadow 2 data structures are exactly the same as Page
Directories, the only difference being the data stored within it. The Shadow 1
tracks which pages were given to child partitions and also
contains some flags related to derivation, such as the is_page_directory() flag,
which defines whether a page has become a child partition or not. The Shadow 2
contains some tracking information, which are the virtual address of a page into
the parent partition's context.

Both of these data structures are inaccessible by any partition.

#### The last linked list structure

The configuration tables linked list contains the physical address of every data
structure page of the current partition (i.e. page directory, page tables,
shadow pages and linked list itself), as well as their virtual address in the
parent partition. As those pages aren't even mapped in a partition, but only are
in their parent, we can't use Shadow 1 or 2 to this purpose. It is structured as
list of <VAddr, PAddr> couples.

```
            |------------------|
            | First free index | 0
    Entry 1 | @V. Page Table   | 1
            | @P. Page Table   | 2
    Entry 2 | @V. Shadow PT1   | 3
            | @P. Shadow PT1   | 4
      ...   |       ...        | ...
            |     (empty)      | maxIndex-1 
            |  @P. Next page   | maxIndex 
            |------------------|
```

This data structure is not accessible by any partition.

## Control flow transfer

### VIDT and *CPU contexts*

Pip requires each partition to provide a VIDT (Virtual Interrupt Descriptor Table) which is a data structure that holds pointers to *cpu contexts*. These CPU contexts are a "snapshot" of the computer's state. When Pip transfers the execution flow, it fetches and applies one of these *contexts* to the machine, optionnally saving the previous one.

```
   |------------------|
   |    ctx_pointer   | 0
   |------------------| 
   |                  |
   |        ...       |
   |                  |
   |                  |
   |------------------|
   |    ctx_pointer   | maxInterrupt
   |------------------|
```

The VIDT address is constant and defined for each architecture. The *contexts* are defined for each architectures too.

*Contexts* live in userland : partitions are free to tamper with them ; if a partition creates a *context*, it must ensure that it is valid, otherwise the partition might trigger a fault when that context is restored.

### Interrupts and fault

Pip does not handle faults or interrupts, it forwards them to the appropriate partition, which should have *contexts* set up to handle them. Interrupts go directly to the root partition, faults and software interrupts go to the partition's parent. If a partition did not set up a *context* to handle the fault/interrupt it receives, the fault is propagated to its parent. This chain reaction can lead as far back as the root partition, which will eventually trigger a system panic if the root partition has not set up a *context* to handle the fault either.

### Automatic context saving

When explicitly asking Pip to transfer the control flow (i.e. by calling `Yield`), a partition can choose where its current context will be saved by providing an index in the VIDT. Pip will look for a valid context pointer at this index. If the pointer is present and valid, Pip will write the context of the current partition to the pointed location.

When a fault/interrupt occurs, Pip will also try to save the current partition's execution state. There are 2 indices reserved in the VIDT for that purpose (which should be defined for each architecture). Then Pip will behave just like explicit calls : it will look for a valid *context* pointer at one of these indices in the VIDT, etc... The index chosen by Pip depends on whether the partition has declared it does not want to be interrupted or not through the `set_int_state` call.
