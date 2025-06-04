---------------------------- MODULE vsfs ----------------------------

EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
  MaxBlocks, \* Total number of blocks (e.g., 8)
  MaxInodes   \* Total number of inodes (e.g., 4)

ASSUME MaxBlocks \in Nat \ {0}
ASSUME MaxInodes \in Nat \ {0}

\* All possible blocks and inode indices
Blocks == 1..MaxBlocks
Inodes == 0..(MaxInodes - 1)

\* Null pointer for unused block slots
Null == 0

\* Maximum direct pointers per inode
MaxDirect == 2

VARIABLES
  freeBlocks,   \* Set of currently free blocks
  InodeTable,   \* Map from inode ID to record: [valid, isDir, size, blocks]
  dir           \* Directory: map from filename (string) to inode number

\* TypeOK invariant: basic well-formedness
TypeOK ==
  /\ freeBlocks \subseteq Blocks
  /\ \A i \in Inodes :
        LET inode == InodeTable[i] IN
        IF inode.valid THEN
            /\ inode.blocks \subseteq Blocks
            /\ inode.blocks \subseteq (Blocks \ freeBlocks)
            /\ inode.size = Cardinality(inode.blocks)
        ELSE
            /\ inode.blocks = {} 
            /\ i \notin DOMAIN dir
  /\ \A name \in DOMAIN dir :
        /\ dir[name] \in Inodes
        /\ InodeTable[dir[name]].valid
        /\ ~InodeTable[dir[name]].isDir

\* Define the algorithm in PlusCal
(*--algorithm VSFS {

variables 
  freeBlocks = {b \in Blocks : TRUE},
  InodeTable = [i \in Inodes |-> [valid |-> (i = 0), 
                                  isDir |-> (i = 0), 
                                  size |-> 0, 
                                  blocks |-> {}]],
  dir = {};

begin

  FileSystem:

  \* Root inode (inode 0) is a valid directory
  InodeTable[0] := [valid |-> TRUE, isDir |-> TRUE, size |-> 0, blocks |-> {}];

  \* Create a file
  createFile:
  if (Len(freeBlocks) >= 1) then
    \* Find first free inode (not 0)
    with (i \in Inodes \ {0}) do
      if (~InodeTable[i].valid) then
        \* Allocate one block
        with (b \in freeBlocks) do
          freeBlocks := freeBlocks \ {b};
          InodeTable[i] := [valid |-> TRUE,
                            isDir |-> FALSE,
                            size |-> 1,
                            blocks |-> {b}];
          dir["file" \o ToString(i)] := i;
        end with;
      end if;
    end with;
  end if;

  \* Done
  skip;

end algorithm; *)

=============================================================================
\* Modification History
\* Last modified Wed Jun 04 20:59:53 IDT 2025 by eitam
\* Created Wed Jun 04 20:59:19 IDT 2025 by eitam
