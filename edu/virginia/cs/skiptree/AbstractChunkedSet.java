package edu.virginia.cs.skiptree;

import java.util.AbstractSet;
import java.util.NavigableSet;

public abstract class AbstractChunkedSet<E> extends AbstractSet<E> implements NavigableSet<E> {

    abstract int expectedNodeSize();
    
}
