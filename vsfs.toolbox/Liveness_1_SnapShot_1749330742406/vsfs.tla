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
    \* Aux variable for multi-step DeleteFile operation
    curFileName = "None";
    curINode = 0;
    curBlock = 0;
    create_stage = "idle";
    write_stage = "idle";
    delete_stage = "idle"; \* "idle", "free_blocks", "invalidate_inode", "remove_dir_entry"
    current_op = "none"; \* "none", "create", "write", "delete"

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
        if(current_op = "none"){
            either {
                current_op := "create";
            }
            or {
                current_op := "write";
            }
            or {
                current_op := "delete";
            }
        }
        else if (current_op = "create") {
            if (create_stage = "idle"){
                with (name \in FileNames) {
                    \* Check if a free inode exists AND the chosen name is not already in use.
                    \* If both conditions are met, non-deterministically pick such an inode 'i'.
                    with (i \in InodeIds \ {curINode} : ~inodes[i].valid /\ name \notin DOMAIN dir) {
                        inodes[i] := [inodes[i] EXCEPT !.valid = TRUE, !.isDir = FALSE, !.size = 0, !.blocks = {}];\* Mark inode as valid, not a directory, size 0, no blocks.
                        curINode := i;
                        curFileName := name;
                        create_stage := "inode_created";
                    };
                    \* return to "none" stage if these conditions weren't met
                    if (create_stage = "idle"){
                        current_op := "none";
                    }
                }
            }
            else if (create_stage = "inode_created"){
                dir := [d \in DOMAIN dir \cup {curFileName} |-> IF d = curFileName THEN curINode ELSE dir[d]];\* Add an entry to the directory mapping the name to the new inode.
                curINode := 0;
                curFileName := "None";
                create_stage := "idle";
                current_op := "none";
            }
        }
        else if (current_op = "write") {
            if (write_stage = "idle") {

                with (name \in DOMAIN dir \ {curFileName}) {
                    \* Get the inode ID for the chosen name.
                    with (i = dir[name]) {
                        \* Check if the inode is valid, not a directory, there are free blocks,
                        \* and the file hasn't reached its maximum block limit.
                        if (inodes[i].valid /\ ~inodes[i].isDir /\ Cardinality(freeBlocks) > 0 /\ Cardinality(inodes[i].blocks) < MaxBlocksPerFile) {
                            with (b \in freeBlocks) { \* Non-deterministically pick a free block, and assign it to the inode
                                \* if we got here, all checks passed and we can write to our file
                                curFileName := name;
                                curINode := i;
                                curBlock := b;
                                freeBlocks := freeBlocks \ {b};
                                write_stage := "block_taken"
                            }
                        }
                    }
                }
            }
            else if (write_stage = "block_taken") {
                inodes[curINode] := [inodes[curINode] EXCEPT !.blocks = @ \cup {curBlock}, !.size = @ + 1];
                curFileName := "None";
                curINode := 0;
                curBlock := 0;
                write_stage := "idle";
                current_op := "none";
            }
        }
        else if (current_op = "delete") {
            if (delete_stage = "idle") {
                with (name \in DOMAIN dir) {
                    curFileName := name;
                    delete_stage := "remove_dir_entry";
                };
                if (delete_stage = "idle") { \* no file to delete
                    current_op := "none";
                }
             } else if (delete_stage = "remove_dir_entry") {
                with (i = dir[curFileName]) {
                    curINode := i;
                    dir := [d \in DOMAIN dir \ {curFileName} |-> dir[d]];
                    delete_stage := "invalidate_inode"; \* Reset for the next deletion
                }
             } else if (delete_stage = "invalidate_inode") {
                inodes[curINode] := [valid |-> FALSE, isDir |-> FALSE, size |-> 0, blocks |-> {}];
                delete_stage := "free_blocks";
             } else if (delete_stage = "free_blocks") {
                freeBlocks := freeBlocks \cup inodes[curINode].blocks;
                delete_stage := "idle";
                curFileName := "None";
                curINode := 0;
                current_op := "none";
             }
        }
\*            print <<"end", op>>;
        }
    }
}
}
*)

\* Manual translation fixes: Remove extra ':'

\* BEGIN TRANSLATION (chksum(pcal) = "1c53cdd3" /\ chksum(tla) \in STRING)
VARIABLES freeBlocks, inodes, dir, curFileName, curINode, curBlock, 
          create_stage, write_stage, delete_stage, current_op

(* define statement *)
MaxBlocksPerFile == 2


vars == << freeBlocks, inodes, dir, curFileName, curINode, curBlock, 
           create_stage, write_stage, delete_stage, current_op >>

Init == (* Global variables *)
        /\ freeBlocks = Blocks \ {1}
        /\ inodes = [i \in InodeIds |->
                           IF i = 0 THEN
                               [valid |-> TRUE, isDir |-> TRUE, size |-> 0, blocks |-> {}]
                           ELSE
                                   [valid |-> FALSE, isDir |-> FALSE, size |-> 0, blocks |-> {}]]
        /\ dir = [n \in {} |-> 0]
        /\ curFileName = "None"
        /\ curINode = 0
        /\ curBlock = 0
        /\ create_stage = "idle"
        /\ write_stage = "idle"
        /\ delete_stage = "idle"
        /\ current_op = "none"

Next == IF current_op = "none"
           THEN /\ \/ /\ current_op' = "create"
                   \/ /\ current_op' = "write"
                   \/ /\ current_op' = "delete"
                /\ UNCHANGED << freeBlocks, inodes, dir, curFileName, 
                                curINode, curBlock, create_stage, 
                                write_stage, delete_stage >>
           ELSE /\ IF current_op = "create"
                      THEN /\ IF create_stage = "idle"
                                 THEN /\ \E name \in FileNames:
                                           /\ \E i \in InodeIds \ {curINode} : ~inodes[i].valid /\ name \notin DOMAIN dir
                                                /\ inodes' = [inodes EXCEPT ![i] = [inodes[i] EXCEPT !.valid = TRUE, !.isDir = FALSE, !.size = 0, !.blocks = {}]]
                                                /\ curINode' = i
                                                /\ curFileName' = name
                                                /\ create_stage' = "inode_created"
                                           /\ IF create_stage' = "idle"
                                                 THEN /\ current_op' = "none"
                                                 ELSE /\ TRUE
                                                      /\ UNCHANGED current_op
                                      /\ dir' = dir
                                 ELSE /\ IF create_stage = "inode_created"
                                            THEN /\ dir' = [d \in DOMAIN dir \cup {curFileName} |-> IF d = curFileName THEN curINode ELSE dir[d]]
                                                 /\ curINode' = 0
                                                 /\ curFileName' = "None"
                                                 /\ create_stage' = "idle"
                                                 /\ current_op' = "none"
                                            ELSE /\ TRUE
                                                 /\ UNCHANGED << dir, 
                                                                 curFileName, 
                                                                 curINode, 
                                                                 create_stage, 
                                                                 current_op >>
                                      /\ UNCHANGED inodes
                           /\ UNCHANGED << freeBlocks, curBlock, 
                                           write_stage, delete_stage >>
                      ELSE /\ IF current_op = "write"
                                 THEN /\ IF write_stage = "idle"
                                            THEN /\ \E name \in DOMAIN dir \ {curFileName}:
                                                      LET i == dir[name] IN
                                                        IF inodes[i].valid /\ ~inodes[i].isDir /\ Cardinality(freeBlocks) > 0 /\ Cardinality(inodes[i].blocks) < MaxBlocksPerFile
                                                           THEN /\ \E b \in freeBlocks:
                                                                     /\ curFileName' = name
                                                                     /\ curINode' = i
                                                                     /\ curBlock' = b
                                                                     /\ freeBlocks' = freeBlocks \ {b}
                                                                     /\ write_stage' = "block_taken"
                                                           ELSE /\ TRUE
                                                                /\ UNCHANGED << freeBlocks, 
                                                                                curFileName, 
                                                                                curINode, 
                                                                                curBlock, 
                                                                                write_stage >>
                                                 /\ UNCHANGED << inodes, 
                                                                 current_op >>
                                            ELSE /\ IF write_stage = "block_taken"
                                                       THEN /\ inodes' = [inodes EXCEPT ![curINode] = [inodes[curINode] EXCEPT !.blocks = @ \cup {curBlock}, !.size = @ + 1]]
                                                            /\ curFileName' = "None"
                                                            /\ curINode' = 0
                                                            /\ curBlock' = 0
                                                            /\ write_stage' = "idle"
                                                            /\ current_op' = "none"
                                                       ELSE /\ TRUE
                                                            /\ UNCHANGED << inodes, 
                                                                            curFileName, 
                                                                            curINode, 
                                                                            curBlock, 
                                                                            write_stage, 
                                                                            current_op >>
                                                 /\ UNCHANGED freeBlocks
                                      /\ UNCHANGED << dir, delete_stage >>
                                 ELSE /\ IF current_op = "delete"
                                            THEN /\ IF delete_stage = "idle"
                                                       THEN /\ \E name \in DOMAIN dir:
                                                                 /\ curFileName' = name
                                                                 /\ delete_stage' = "remove_dir_entry"
                                                            /\ IF delete_stage' = "idle"
                                                                  THEN /\ current_op' = "none"
                                                                  ELSE /\ TRUE
                                                                       /\ UNCHANGED current_op
                                                            /\ UNCHANGED << freeBlocks, 
                                                                            inodes, 
                                                                            dir, 
                                                                            curINode >>
                                                       ELSE /\ IF delete_stage = "remove_dir_entry"
                                                                  THEN /\ LET i == dir[curFileName] IN
                                                                            /\ curINode' = i
                                                                            /\ dir' = [d \in DOMAIN dir \ {curFileName} |-> dir[d]]
                                                                            /\ delete_stage' = "invalidate_inode"
                                                                       /\ UNCHANGED << freeBlocks, 
                                                                                       inodes, 
                                                                                       curFileName, 
                                                                                       current_op >>
                                                                  ELSE /\ IF delete_stage = "invalidate_inode"
                                                                             THEN /\ inodes' = [inodes EXCEPT ![curINode] = [valid |-> FALSE, isDir |-> FALSE, size |-> 0, blocks |-> {}]]
                                                                                  /\ delete_stage' = "free_blocks"
                                                                                  /\ UNCHANGED << freeBlocks, 
                                                                                                  curFileName, 
                                                                                                  curINode, 
                                                                                                  current_op >>
                                                                             ELSE /\ IF delete_stage = "free_blocks"
                                                                                        THEN /\ freeBlocks' = (freeBlocks \cup inodes[curINode].blocks)
                                                                                             /\ delete_stage' = "idle"
                                                                                             /\ curFileName' = "None"
                                                                                             /\ curINode' = 0
                                                                                             /\ current_op' = "none"
                                                                                        ELSE /\ TRUE
                                                                                             /\ UNCHANGED << freeBlocks, 
                                                                                                             curFileName, 
                                                                                                             curINode, 
                                                                                                             delete_stage, 
                                                                                                             current_op >>
                                                                                  /\ UNCHANGED inodes
                                                                       /\ dir' = dir
                                            ELSE /\ TRUE
                                                 /\ UNCHANGED << freeBlocks, 
                                                                 inodes, 
                                                                 dir, 
                                                                 curFileName, 
                                                                 curINode, 
                                                                 delete_stage, 
                                                                 current_op >>
                                      /\ UNCHANGED << curBlock, write_stage >>
                           /\ UNCHANGED create_stage

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
      
AllAllocatedBlocksAreUsed ==
    /\ \A b \in Blocks \ freeBlocks:
       \E i \in DOMAIN inodes:
         inodes[i].valid /\ b \in inodes[i].blocks
         
SomeAllocatedBlockIsUnused == ~AllAllocatedBlocksAreUsed
      
      
DeleteisUnsafe ==
    []((current_op = "delete" /\ delete_stage = "invalidate_inode") => SomeAllocatedBlockIsUnused)

\* Liveness properties

\* 

AlwaysGetsToIdle ==
  []<>(current_op = "none")

AllFilesEventuallyCreated ==
  <> \A name \in FileNames : name \in DOMAIN dir

AllFilesEventuallyDeleted ==
  <> \A name \in FileNames : name \in DOMAIN dir
  
SpecWithFairness == Spec 
    /\ AllFilesEventuallyCreated
  
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
\* Last modified Sun Jun 08 00:12:15 IDT 2025 by omerzohar
\* Last modified Fri Jun 06 18:35:58 IDT 2025 by eitam
\* Created Thu Jun 05 20:42:58 IDT 2025 by eitam
