# vec-graph

```toml
[dependencies]
vec-graph = {"git": "https://github.com/emallson/vec-graph.git"}
```

This library gives an alternate `Graph` implementation implementing the
traits from [`petgraph`](https://docs.rs/petgraph/). This implementation uses
a more traditional edge-list style which has performed better for very
specialized use-cases in my work (specifically, when working with very large
(40GB+ in memory) graphs where frequent enumeration of the in/out edge lists of
random nodes is needed). **Do not simply insert this blindly and assume it will
be faster!** For *almost all* cases I've tried, `petgraph`'s default
implementation is faster.

## Usage

```rust
extern crate petgraph;
extern crate vec_graph;

use petgraph::prelude::*;

use vec_graph::{NodeIndex, EdgeIndex, Graph}; 
// or: use vec_graph::{NodeIndex, EdgeIndex, VecGraph};
```

## License
Copyright (c) 2017, J. David Smith
All rights reserved.

Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:

1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.

3. Neither the name of the copyright holder nor the names of its contributors may be used to endorse or promote products derived from this software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
