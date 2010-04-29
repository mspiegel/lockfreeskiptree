package edu.virginia.cs.skiptree;

import java.util.concurrent.ConcurrentNavigableMap;

public interface ConcurrentChunkedMap<K,V> extends ConcurrentNavigableMap<K,V> {
    
    int expectedNodeSize();
    
    /**
     * @throws ClassCastException       {@inheritDoc}
     * @throws NullPointerException     {@inheritDoc}
     * @throws IllegalArgumentException {@inheritDoc}
     */
    ConcurrentChunkedMap<K,V> subMap(K fromKey, boolean fromInclusive,
                                       K toKey,   boolean toInclusive);
    
    /**
     * @throws ClassCastException       {@inheritDoc}
     * @throws NullPointerException     {@inheritDoc}
     * @throws IllegalArgumentException {@inheritDoc}
     */
    ConcurrentChunkedMap<K,V> headMap(K toKey, boolean inclusive);
    
    /**
     * @throws ClassCastException       {@inheritDoc}
     * @throws NullPointerException     {@inheritDoc}
     * @throws IllegalArgumentException {@inheritDoc}
     */
    ConcurrentChunkedMap<K,V> tailMap(K fromKey, boolean inclusive);

    /**
     * @throws ClassCastException       {@inheritDoc}
     * @throws NullPointerException     {@inheritDoc}
     * @throws IllegalArgumentException {@inheritDoc}
     */
    ConcurrentChunkedMap<K,V> subMap(K fromKey, K toKey);

    /**
     * @throws ClassCastException       {@inheritDoc}
     * @throws NullPointerException     {@inheritDoc}
     * @throws IllegalArgumentException {@inheritDoc}
     */
    ConcurrentChunkedMap<K,V> headMap(K toKey);

    /**
     * @throws ClassCastException       {@inheritDoc}
     * @throws NullPointerException     {@inheritDoc}
     * @throws IllegalArgumentException {@inheritDoc}
     */
    ConcurrentChunkedMap<K,V> tailMap(K fromKey);
    
    ConcurrentChunkedMap<K,V> descendingMap();    
    
}
