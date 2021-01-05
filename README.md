Reliable C Portable Runtime
===========================

The Reliable C Portable Runtime provides features and patterns to work with the
Idiomatic Resource-Oriented C style.  The most important structure is the
`resource` structure, which is used to model resources with a model checker.

Features
--------

* `allocator` - abstraction to work with different allocation strategies.
* `resource` - pattern for dealing with memory and external resources
* `status` - mechanism for registering unique status codes and error codes
* `abstract_factory` - mechanism for registering and getting factories for
  specific features
* `bloom_filter` - filter for quickly checking for membership which may have
  false positives
* `slist` and `list` - single and doubly linked list
* `dict` (hash map) - hash map dictionary
* `rbtree` - red / black tree
* `map` - dictionary based on the red / black tree
* `set` - set based on the red / black tree
* `thread` - a threading library including threads, mutexes, and conditionals.
