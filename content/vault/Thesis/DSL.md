# A DSL for bidirectional programs

Using lenses to write programs can be quite tedious due to the extensive use of
combinators that need to be carefully threaded together. Haskell probably would not have reached the popularity that it enjoys if it relied on SK combinators.
To facilitate the writing of programs involving lenses, I present a DSL that I will use for all the demos in the next chapter.

I've arranged this chapter in a way that provides a gradual progression of understanding that mimics the way I have internalised the topic. If you do not need such progression, skip to the last section.

Because we've already seen [lenses](../src/Optics/Lens.idr.md) and [dependent lenses](../src/Data/Container/Morphism.idr.md) we are going to move on from there and introduce [van-laarhoven lenses](../src/Optics/VanLaarhoven.idr.md).
Van-Laarhoven lenses have been the object of a lot of research and one of them is [_pointful_](../src/Optics/VanLaarhoven.idr.md#pointful) (or "less pointless") lenses.

Pointful lenses already gives us a DSL (Domain Specific Language) to write lenses, but they are limited to non-dependent lenses. To make up for that, I will generalise them and show that they are equivalent to [closed lenses](../src/Data/Container/Morphism/Closed.idr.md), an existing definition of lenses related to dependent lenses.

The last step is the introduction of [linear lenses](../src/Data/Container/Morphism/Linear.idr.md), a new (to my knowledge) type of container morphism that captures the DSL capabilities of pointful lenses, is compatible with our understanding of dependent/closed lenses, and faithfully represents the constraints of a domain specific language for string-diagrams of lenses.
