Model Checking RCPR
===================

To improve RCPR's safety, I have started a project to modernize model checking
in this library. To model check this library, I use [CBMC][cbmc].

[cmbc]: https://www.cprover.org/cbmc/

Public Methods
--------------

This file tracks the current progress of this effort. The first goal of this
effort is to ensure that every public function has a function contract, and that
every public type has a validating model checking property associated with it
that verifies invariants relating to that type.

This effort also includes the creation of shadow methods that can be used by
downstream projects. These shadow methods enforce the same function contracts
found in the headers and are installed in the `share/rcpr/models/shadow`
directory.

The following table breaks down progress by header.

| Header                                            | Progress %              |
| :-------------------------------------------------| ----------------------: |
| `include/rcpr/fiber_fwd.h`                        | $\color{red}{0}$ %      |
| `include/rcpr/thread.h`                           | $\color{red}{0}$ %      |
| `include/rcpr/component.h`                        | $\color{red}{0}$ %      |
| `include/rcpr/fiber/disciplines/psock_io.h`       | $\color{red}{0}$ %      |
| `include/rcpr/fiber/disciplines/message.h`        | $\color{red}{0}$ %      |
| `include/rcpr/fiber/disciplines/condition.h`      | $\color{red}{0}$ %      |
| `include/rcpr/fiber/disciplines/management.h`     | $\color{red}{0}$ %      |
| `include/rcpr/status/thread.h`                    | $\color{red}{0}$ %      |
| `include/rcpr/status/string.h`                    | $\color{red}{0}$ %      |
| `include/rcpr/status/psock.h`                     | $\color{red}{0}$ %      |
| `include/rcpr/status/socket_utilities.h`          | $\color{red}{0}$ %      |
| `include/rcpr/status/fiber.h`                     | $\color{red}{0}$ %      |
| `include/rcpr/status/message.h`                   | $\color{red}{0}$ %      |
| `include/rcpr/status/general.h`                   | $\color{red}{0}$ %      |
| `include/rcpr/status/condition.h`                 | $\color{red}{0}$ %      |
| `include/rcpr/status/uuid.h`                      | $\color{red}{0}$ %      |
| `include/rcpr/status/rbtree.h`                    | $\color{red}{0}$ %      |
| `include/rcpr/status/stack.h`                     | $\color{red}{0}$ %      |
| `include/rcpr/status/auto_reset_trigger.h`        | $\color{red}{0}$ %      |
| `include/rcpr/status.h`                           | $\color{red}{0}$ %      |
| `include/rcpr/string.h`                           | $\color{red}{0}$ %      |
| `include/rcpr/shadow/model_tag.h`                 | $\color{red}{0}$ %      |
| `include/rcpr/shadow/allocator.h`                 | $\color{red}{0}$ %      |
| `include/rcpr/shadow/valid_range.h`               | $\color{red}{0}$ %      |
| `include/rcpr/model_assert.h`                     | $\color{red}{0}$ %      |
| `include/rcpr/compare.h`                          | $\color{red}{0}$ %      |
| `include/rcpr/list.h`                             | $\color{red}{0}$ %      |
| `include/rcpr/psock.h`                            | $\color{red}{0}$ %      |
| `include/rcpr/socket_utilities.h`                 | $\color{red}{0}$ %      |
| `include/rcpr/function_decl.h`                    | $\color{red}{0}$ %      |
| `include/rcpr/fiber.h`                            | $\color{red}{0}$ %      |
| `include/rcpr/macro_tricks.h`                     | $\color{red}{0}$ %      |
| `include/rcpr/resource/protected.h`               | $\color{red}{0}$ %      |
| `include/rcpr/slist.h`                            | $\color{red}{0}$ %      |
| `include/rcpr/byteswap.h`                         | $\color{red}{0}$ %      |
| `include/rcpr/resource.h`                         | $\color{red}{0}$ %      |
| `include/rcpr/vtable.h`                           | $\color{red}{0}$ %      |
| `include/rcpr/allocator.h`                        | $\color{red}{0}$ %      |
| `include/rcpr/message.h`                          | $\color{red}{0}$ %      |
| `include/rcpr/condition.h`                        | $\color{red}{0}$ %      |
| `include/rcpr/control.h`                          | $\color{red}{0}$ %      |
| `include/rcpr/bigint.h`                           | $\color{red}{0}$ %      |
| `include/rcpr/uuid.h`                             | $\color{red}{0}$ %      |
| `include/rcpr/rbtree.h`                           | $\color{red}{0}$ %      |
| `include/rcpr/stack.h`                            | $\color{red}{0}$ %      |
| `include/rcpr/auto_reset_trigger.h`               | $\color{red}{0}$ %      |
| `include/rcpr/function_contracts.h`               | $\color{red}{0}$ %      |
| `include/rcpr/queue.h`                            | $\color{red}{0}$ %      |

Private Methods
---------------

The second goal of this project ensures that all private methods -- at least
those in C -- are also model checked.
