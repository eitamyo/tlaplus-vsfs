---------------------------- MODULE vsfs ----------------------------

EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS 
    Blocks,     \* e.g., {1,2,3,4,5,6,7,8} - The set of all data blocks in the file system.
    InodeIds,   \* e.g., 0..N-1 - The set of all possible inode identifiers.
    FileNames   \* e.g., {"file1", "file2", "dir1"} - The set of all possible file names.

ASSUME FileNames \subseteq STRING /\ FileNames # {}

(*--fair algorithm FSModel {
\* File System Model Algorithm: Simulates basic file system operations.

variables 
    \* freeBlocks: A set of data blocks that are currently available for allocation.
    freeBlocks = Blocks \ {1}, \* Initialize freeBlocks to all blocks except block 1 (reserved, e.g., for superblock).
    \* inodes: A mapping from InodeId to a record representing an inode.
    \* Each inode record has fields:
    \* - valid: BOOLEAN (TRUE if the inode is in use, FALSE otherwise)
    \* - isDir: BOOLEAN (TRUE if the inode represents a directory, FALSE for a regular file)
    \* - size: NATURAL (The logical size of the file/directory in abstract units)
    \* - blocks: Set(Blocks) (The set of data blocks allocated to this inode)
    inodes = [i \in InodeIds |->
                    IF i = 0 THEN
                        [valid |-> TRUE, isDir |-> TRUE, size |-> 0, blocks |-> {}] \* Inode 0 is the root directory, initially valid and empty.
                    ELSE
                            [valid |-> FALSE, isDir |-> FALSE, size |-> 0, blocks |-> {}]], \* All other inodes are initially invalid/free.
    \* dir: A mapping from file/directory name (STRING) to its InodeId.
    dir = [n \in {} |-> 0]; \* Initialize directory as empty (no entries).

define {
    MaxBlocksPerFile == 2 \* Defines the maximum number of data blocks a single file can use.
}


{
Main:
    \* The main loop of the file system model, continuously performing operations.
    while (TRUE) {
        \* Non-deterministically choose an operation to perform.
\*        with (op \in {"CreateFile", "WriteFile", "ReadFile", "DeleteFile"}) {
\*            if (op = "CreateFile") {
        either {
CreateFileOp:
            \* Non-deterministically choose a file name.
            with (name \in FileNames) {
                \* Check if a free inode exists AND the chosen name is not already in use.
                \* If both conditions are met, non-deterministically pick such an inode 'i'.
                with (i \in InodeIds : ~inodes[i].valid /\ name \notin DOMAIN dir) {
                    inodes[i] := [inodes[i] EXCEPT !.valid = TRUE, !.isDir = FALSE, !.size = 0, !.blocks = {}];\* Mark inode as valid, not a directory, size 0, no blocks.
                    dir := [d \in DOMAIN dir \cup {name} |-> IF d = name THEN i ELSE dir[d]];\* Add an entry to the directory mapping the name to the new inode.
                }
            }
        }
\*            else if (op = "WriteFile") {
        or {
WriteFileOp:
            \* Non-deterministically choose an existing file name.
            with (name \in DOMAIN dir) {
                \* Get the inode ID for the chosen name.
                with (i = dir[name]) {
                    \* Check if the inode is valid, not a directory, there are free blocks,
                    \* and the file hasn't reached its maximum block limit.
                    if (inodes[i].valid /\ ~inodes[i].isDir /\ Cardinality(freeBlocks) > 0 /\ Cardinality(inodes[i].blocks) < MaxBlocksPerFile) {
                        with (b \in freeBlocks) { \* Non-deterministically pick a free block, and assign it to the inode
                            freeBlocks := freeBlocks \ {b};
                            inodes[i] := [inodes[i] EXCEPT !.blocks = @ \cup {b}, !.size = @ + 1];
                        }
                    }
                }
            }
        }
\*            else if (op = "ReadFile") {
        or {
ReadFileOp:
            with (name \in DOMAIN dir) {
                with (i = dir[name]) {
                    \* Non-deterministically choose a valid offset within the file's logical size.
                    with (offset \in 0..(inodes[i].size - 1)) {
                        skip; \* 'skip' means no state change occurs, just simulating the action.
                    }
                }
            }
        }
\*            else if (op = "DeleteFile") {
        or {
        
DeleteFileOp:
                with (name \in DOMAIN dir) {
                    with (i = dir[name]) {
                        freeBlocks := freeBlocks \cup inodes[i].blocks; \* Return all blocks associated with the inode to freeBlocks.
                        dir := [d \in DOMAIN dir \ {name} |-> dir[d]]; \* Remove the file's entry from the directory
                        inodes[i] := [valid |-> FALSE, isDir |-> FALSE, size |-> 0, blocks |-> {}]; \* Invalidate the inode and reset its fields.
                    }
                }
\*            };
        }
            
\*            print <<"end", op>>;
        }
    }
}
}
*)

\* Manual translation fixes: Remove extra ':'

\* BEGIN TRANSLATION (chksum(pcal) = "c5d56722" /\ chksum(tla) \in STRING)
VARIABLES freeBlocks, inodes, dir, pc

(* define statement *)
MaxBlocksPerFile == 2


vars == << freeBlocks, inodes, dir, pc >>

Init == (* Global variables *)
        /\ freeBlocks = Blocks \ {1}
        /\ inodes = [i \in InodeIds |->
                           IF i = 0 THEN
                               [valid |-> TRUE, isDir |-> TRUE, size |-> 0, blocks |-> {}]
                           ELSE
                                   [valid |-> FALSE, isDir |-> FALSE, size |-> 0, blocks |-> {}]]
        /\ dir = [n \in {} |-> 0]
        /\ pc = "Main"

Main == /\ pc = "Main"
        /\ \/ /\ pc' = "CreateFileOp"
           \/ /\ pc' = "WriteFileOp"
           \/ /\ pc' = "ReadFileOp"
           \/ /\ pc' = "DeleteFileOp"
        /\ UNCHANGED << freeBlocks, inodes, dir >>

CreateFileOp == /\ pc = "CreateFileOp"
                /\ \E name \in FileNames:
                     \E i \in InodeIds : ~inodes[i].valid /\ name \notin DOMAIN dir
                       /\ inodes' = [inodes EXCEPT ![i] = [inodes[i] EXCEPT !.valid = TRUE, !.isDir = FALSE, !.size = 0, !.blocks = {}]]
                       /\ dir' = [d \in DOMAIN dir \cup {name} |-> IF d = name THEN i ELSE dir[d]]
                /\ pc' = "Main"
                /\ UNCHANGED freeBlocks

WriteFileOp == /\ pc = "WriteFileOp"
               /\ \E name \in DOMAIN dir:
                    LET i == dir[name] IN
                      IF inodes[i].valid /\ ~inodes[i].isDir /\ Cardinality(freeBlocks) > 0 /\ Cardinality(inodes[i].blocks) < MaxBlocksPerFile
                         THEN /\ \E b \in freeBlocks:
                                   /\ freeBlocks' = freeBlocks \ {b}
                                   /\ inodes' = [inodes EXCEPT ![i] = [inodes[i] EXCEPT !.blocks = @ \cup {b}, !.size = @ + 1]]
                         ELSE /\ TRUE
                              /\ UNCHANGED << freeBlocks, inodes >>
               /\ pc' = "Main"
               /\ dir' = dir

ReadFileOp == /\ pc = "ReadFileOp"
              /\ \E name \in DOMAIN dir:
                   LET i == dir[name] IN
                     \E offset \in 0..(inodes[i].size - 1):
                       TRUE
              /\ pc' = "Main"
              /\ UNCHANGED << freeBlocks, inodes, dir >>

DeleteFileOp == /\ pc = "DeleteFileOp"
                /\ \E name \in DOMAIN dir:
                     LET i == dir[name] IN
                       /\ freeBlocks' = (freeBlocks \cup inodes[i].blocks)
                       /\ dir' = [d \in DOMAIN dir \ {name} |-> dir[d]]
                       /\ inodes' = [inodes EXCEPT ![i] = [valid |-> FALSE, isDir |-> FALSE, size |-> 0, blocks |-> {}]]
                /\ pc' = "Main"

Next == Main \/ CreateFileOp \/ WriteFileOp \/ ReadFileOp \/ DeleteFileOp

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

\* END TRANSLATION 

\* TLC Invariants

\* Safety properties

\* No two inodes point to the same block
NoDoubleAllocation ==
  \A i \in DOMAIN inodes:
    \A j \in DOMAIN inodes:
      (i # j) => (inodes[i].blocks \cap inodes[j].blocks = {})

\* All directory entries point to valid inodes
AllDirEntriesPointToValidInodes ==
  \A name \in DOMAIN dir:
    LET i == dir[name] IN inodes[i].valid = TRUE
    
\* Block is used iff it is allocated to an inode
AllUsedBlocksAreAllocated ==
  /\ \A i \in DOMAIN inodes:
       inodes[i].valid =>
         \A b \in inodes[i].blocks: b \notin freeBlocks
  /\ \A b \in freeBlocks:
       \A i \in DOMAIN inodes:
         inodes[i].valid =>
           b \notin inodes[i].blocks

\* No free inode is referenced by a directory entry or has allocated blocks
FreeInodesAreUnreferencedAndBlockless ==
  \A i \in DOMAIN inodes:
    ~inodes[i].valid =>
      /\ \A name \in DOMAIN dir: dir[name] # i
      /\ inodes[i].blocks = {}
      

\* Liveness properties

\* 
CanCreate(name) == 
  name \notin DOMAIN dir /\ (\E i \in InodeIds : ~inodes[i].valid)

FileCreationLiveness ==
  \A name \in FileNames : 
    [] (CanCreate(name)) => <> (name \in DOMAIN dir)

FileDeletionLiveness ==
  \A name \in FileNames :
    [] (name \in DOMAIN dir) => <> (name \notin DOMAIN dir)

=============================================================================
\* Modification History
\* Last modified Fri Jun 06 13:36:55 IDT 2025 by eitam
\* Created Thu Jun 05 20:42:58 IDT 2025 by eitam
