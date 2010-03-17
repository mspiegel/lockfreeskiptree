/*
 * Written by Michael Spiegel with assistance from Doug Lea 
 * and members of JCP JSR-166 Expert Group and released
 * to the public domain, as explained at
 * http://creativecommons.org/licenses/publicdomain
 */

package edu.virginia.cs.skiptree;
import java.util.*;
import java.util.concurrent.*;
import java.util.concurrent.atomic.*;


/**
 * A scalable concurrent {@link ConcurrentNavigableMap} implementation.
 * The map is sorted according to the {@linkplain Comparable natural
 * ordering} of its keys, or by a {@link Comparator} provided at map
 * creation time, depending on which constructor is used.
 *
 * <p>This class implements a concurrent variant of skip trees,
 * a cache-conscious isomorphism of <a
 * href="http://www.cs.umd.edu/~pugh/">skip lists</a> providing
 * expected average <i>log(n)</i> time cost for the
 * <tt>containsKey</tt>, <tt>get</tt>, <tt>put</tt> and
 * <tt>remove</tt> operations and their variants.  Insertion, removal,
 * update, and access operations safely execute concurrently by
 * multiple threads.  Iterators are <i>weakly consistent</i>, returning
 * elements reflecting the state of the map at some point at or since
 * the creation of the iterator.  They do <em>not</em> throw {@link
 * ConcurrentModificationException}, and may proceed concurrently with
 * other operations. Ascending key ordered views and their iterators
 * are faster than descending ones.
 *
 * <p>All <tt>Map.Entry</tt> pairs returned by methods in this class
 * and its views represent snapshots of mappings at the time they were
 * produced. They do <em>not</em> support the <tt>Entry.setValue</tt>
 * method. (Note however that it is possible to change mappings in the
 * associated map using <tt>put</tt>, <tt>putIfAbsent</tt>, or
 * <tt>replace</tt>, depending on exactly which effect you need.)
 *
 * <p>Beware that, unlike in most collections, the <tt>size</tt>
 * method is <em>not</em> a constant-time operation. Because of the
 * asynchronous nature of these maps, determining the current number
 * of elements requires a traversal of the elements.  Additionally,
 * the bulk operations <tt>putAll</tt>, <tt>equals</tt>, and
 * <tt>clear</tt> are <em>not</em> guaranteed to be performed
 * atomically. For example, an iterator operating concurrently with a
 * <tt>putAll</tt> operation might view only some of the added
 * elements.
 *
 * <p>This class and its views and iterators implement all of the
 * <em>optional</em> methods of the {@link Map} and {@link Iterator}
 * interfaces. Like most other concurrent collections, this class does
 * <em>not</em> permit the use of <tt>null</tt> keys or values because some
 * null return values cannot be reliably distinguished from the absence of
 * elements.
 * 
 * @author Michael Spiegel
 * @param <K> the type of keys maintained by this map
 * @param <V> the type of mapped values
 */
@SuppressWarnings("unchecked")
public class ConcurrentSkipTreeMap<K,V> extends AbstractMap<K,V> 
    implements ConcurrentNavigableMap<K,V>,
    Cloneable,
    java.io.Serializable    {
    
    /*
     * This class implements a lock-free skip tree, a concurrent
     * data structure that shares similarities with a skip list 
     * and a B^link-tree. The skip tree is a multiway search tree.
     * Each node in the tree stores a volatile reference to a container
     * that stores multiple data items. The skip tree improves spatial
     * locality by storing multiple items per container.
     * 
     * The lock-free skip tree is explained in "Lock-Free Multiway Search Trees"
     * (Spiegel & Reynolds, 2010) submitted for publication. The
     * skip tree was defined by (Messeguer, 1997). An isomorphism between
     * the skip list and the B-tree has been noted in other sources, including
     * (Munro, Papadakis, and Sedgewick, 1992). The skip list was defined by
     * (Pugh, 1990). The "link" pointer was first used in the definition of
     * the B^link-tree by (Lehman and Yao, 1981) and refined by (Sagiv, 1985).
     * The Michael-Harris algorithm for lock-free linked lists can be found
     * in (Michael, 2002) and (Harris, 2001).
     * 
     * The lock-free skip tree consists of several linked lists 
     * stacked on top of each other. Each node holds a volatile reference 
     * to a container. Each container stores an array of keys, an array
     * of values, an array of child references, and a link to the next 
     * node at the current level. Like a B+-tree, in the skip tree
     * (key, value) pairs are stored in the leaves of the tree.
     * 
     * The lock-free skip tree has relaxed structural properties
     * that allow atomic operations to modify the tree without
     * invalidating the consistency of the tree. Optimal paths
     * through the tree are temporarily violated by mutation
     * operations, and eventually restored using online
     * node compaction.
     * 
     * To explain the structural properties of the skip tree it 
     * will be useful to define the "tail set" of a node n at level i.
     * The tail set of n is the set that contains n and all nodes 
     * subsequent to n at level i.
     * 
     * The lock-free skip tree is defined as follows:
     * 
     * (D1) Each level contains the element +infinity at the
     *      last element of the last node. The element
     *      +infinity appears exactly once for each level.
     * (D2) The leaf level does not contain duplicate elements.
     * (D3) For each level, given some 'k' there exists
     *      exactly one pair of adjacent elements 'A' and
     *      'B' such that A < k <= B.
     * (D4) Given levels i and i − 1 and some 'k',
     *      there exist exactly two pairs of adjacent elements
     *      (A_i, B_i) and (A_i−1, B_i−1) that satisfy
     *      property (D3). If 'source' is the child node
     *      between elements A_i and B_i, and 'target' is
     *      the node that contains elements B_i−1, then
     *      'target' is in the tail set of 'source'.
     * (D5) For each node, given some 'k' such that k
     *      is greater than or equal to all the elements
     *      of the node, then k will always be greater
     *      than or equal to all elements of the node in
     *      all possible futures.
     */
    
    private static final int logAvgLength = 5; // log_2 of the average node length
    private static final int avgLength = (1 << logAvgLength);
    private static final int avgLengthMinusOne = (avgLength - 1);
    
    private static final long serialVersionUID = -8380871345797974329L;

    /**
     * The topmost node of the skip tree.
     */
    private transient volatile HeadNode<K,V> root;
    
    /**
     * A reference to the start of the leaf level
     */
    private transient volatile Node<K,V> leafHead;

    /**
     * Generates the initial random seed for the cheaper per-instance
     * random number generators used in randomLevel.
     */
    private static final Random seedGenerator = new Random();        
    
    /**
     * Seed for simple random number generator.  Not volatile since it
     * doesn't matter too much if different threads don't see updates.
     */
    private transient int randomSeed;

    /**
     * The comparator used to maintain order in this map, or null
     * if using natural ordering.
     * @serial
     */
    private final Comparator<? super K> comparator;    
    
    /** CAS for volatile root reference */
    private static final AtomicReferenceFieldUpdater<ConcurrentSkipTreeMap, HeadNode>
        rootUpdater = AtomicReferenceFieldUpdater.newUpdater(
                ConcurrentSkipTreeMap.class, HeadNode.class, "root");
    
    /** CAS for volatile leafHead reference */
    private static final AtomicReferenceFieldUpdater<ConcurrentSkipTreeMap, Node>
        leafHeadUpdater = AtomicReferenceFieldUpdater.newUpdater(
                ConcurrentSkipTreeMap.class, Node.class, "leafHead");
    
    /** Lazily initialized key set */
    private transient KeySet keySet;
    /** Lazily initialized entry set */
    private transient EntrySet entrySet;
    /** Lazily initialized values collection */
    private transient Values valuesCollection;
    /** Lazily initialized descending key set */
    private transient ConcurrentNavigableMap<K,V> descendingMap;
    
    /** if non-null, then always return this proxy instead of storing values */
    private final V valueProxy;
    
    /**
     * Initializes or resets state. Needed by constructors, clone,
     * clear, readObject. and ConcurrentSkipListSet.clone.
     * (Note that comparator must be separately initialized.)
     */
    final void initialize() {
        keySet = null;
        entrySet = null;
        valuesCollection = null;
        descendingMap = null;        
        randomSeed = seedGenerator.nextInt() | 0x0100;
        Object[] keys = new Object[1];
        Object[] values = (valueProxy == null) ? new Object[1] : null;
        keys[0] = PositiveInfinity.INSTANCE;
        Contents<K,V> contents = new Contents<K,V>(keys, values, null, null);
        Node<K,V> node = new Node<K,V>(contents);
        rootUpdater.set(this, new HeadNode<K,V>(node, 0));
        leafHeadUpdater.set(this, node);
    }

    /* ---------------- Constructors -------------- */
    
    
    public ConcurrentSkipTreeMap() {
        this.comparator = null;
        this.valueProxy = null;
        initialize();      
    }
    
    protected ConcurrentSkipTreeMap(V proxy) {
        this.comparator = null;
        this.valueProxy = proxy;
        initialize();
    }
    
    /**
     * Constructs a new, empty map, sorted according to the specified
     * comparator.
     *
     * @param comparator the comparator that will be used to order this map.
     *        If <tt>null</tt>, the {@linkplain Comparable natural
     *        ordering} of the keys will be used.
     */
    public ConcurrentSkipTreeMap(Comparator<? super K> comparator) {
        this.comparator = comparator;
        this.valueProxy = null;
        initialize();
    }
    
    protected ConcurrentSkipTreeMap(Comparator<? super K> comparator, V proxy) {
        this.comparator = comparator;
        this.valueProxy = proxy;        
        initialize();
    }
    
    /**
     * Constructs a new map containing the same mappings as the given map,
     * sorted according to the {@linkplain Comparable natural ordering} of
     * the keys.
     *
     * @param  m the map whose mappings are to be placed in this map
     * @throws ClassCastException if the keys in <tt>m</tt> are not
     *         {@link Comparable}, or are not mutually comparable
     * @throws NullPointerException if the specified map or any of its keys
     *         or values are null
     */
    public ConcurrentSkipTreeMap(Map<? extends K, ? extends V> m) {
        this.comparator = null;
        this.valueProxy = null;
        initialize();
        putAll(m);
    }

    protected ConcurrentSkipTreeMap(Map<? extends K, ? extends V> m, V proxy) {
        this.comparator = null;
        this.valueProxy = proxy;
        initialize();
        putAll(m);
    }
    
    /**
     * Constructs a new map containing the same mappings and using the
     * same ordering as the specified sorted map.
     *
     * @param m the sorted map whose mappings are to be placed in this
     *        map, and whose comparator is to be used to sort this map
     * @throws NullPointerException if the specified sorted map or any of
     *         its keys or values are null
     */
    public ConcurrentSkipTreeMap(SortedMap<K, ? extends V> m) {
        this.comparator = m.comparator();
        this.valueProxy = null;
        initialize();
        buildFromSorted(m);
    }
    
    protected ConcurrentSkipTreeMap(SortedMap<K, ? extends V> m, V proxy) {
        this.comparator = m.comparator();
        this.valueProxy = proxy;
        initialize();
        buildFromSorted(m);
    }
    
    /**
     * Returns a shallow copy of this <tt>ConcurrentSkipListMap</tt>
     * instance. (The keys and values themselves are not cloned.)
     *
     * @return a shallow copy of this map
     */
    public ConcurrentSkipTreeMap<K,V> clone() {
        ConcurrentSkipTreeMap<K,V> clone = null;
        try {
            clone = (ConcurrentSkipTreeMap<K,V>) super.clone();
        } catch (CloneNotSupportedException e) {
            throw new InternalError();
        }

        clone.initialize();
        clone.buildFromSorted(this);
        return clone;
    }    
    
    /**
     * Streamlined bulk insertion to initialize from elements of
     * given sorted map.  Call only from constructor or clone
     * method.
     */
    private void buildFromSorted(SortedMap<K, ? extends V> map) {
        if (map == null)
            throw new NullPointerException();
        Iterator<? extends Map.Entry<? extends K, ? extends V>> it =
            map.entrySet().iterator();
        Object[] keys = new Object[avgLength];
        Object[] values = (valueProxy == null) ? new Object[avgLength] : null;
        Node<K,V> current = null;
        int leafCount = 0, totalCount = 0;
        while (it.hasNext()) {
            Map.Entry<? extends K, ? extends V> entry = it.next();
            K nextKey = entry.getKey();
            V nextValue = (valueProxy == null) ? entry.getValue() : valueProxy;
            keys[leafCount] = nextKey;
            if (valueProxy == null) values[leafCount] = nextValue;
            leafCount++; 
            totalCount++;
            if (leafCount % avgLength == 0) {
                leafCount = 0;
                current = buildFromSortedLeaf(keys, values, current);
                buildFromSortedNonLeaf(totalCount, nextKey);    
                keys = new Object[avgLength];
                values = (valueProxy == null) ? new Object[avgLength] : null;                
            }
        }
        if (leafCount > 0) {
            keys = Arrays.copyOf(keys, leafCount);
            if (valueProxy == null) {
                values = Arrays.copyOf(values, leafCount);
            }
            buildFromSortedLeaf(keys, values, current);
        }
    }

    private Node<K, V> buildFromSortedLeaf(Object[] keys, Object[] values,
            Node<K, V> current) {
        if (current == null) {
            Node<K,V> leafHead = this.leafHead;
            Contents<K,V> contents = new Contents<K,V>(keys, values, null, leafHead);
            Node<K,V> newLeafHead = new Node<K,V>(contents);
            HeadNode<K,V> newHeadNode = new HeadNode<K,V>(newLeafHead, 0);                    
            leafHeadUpdater.set(this, newLeafHead);
            rootUpdater.set(this, newHeadNode);                    
            current = newLeafHead;
        } else {
            Contents<K,V> contents = current.contents;
            Contents<K,V> newcontents = new Contents<K,V>(keys, values, null, contents.link);
            Node<K,V> newnode = new Node<K,V>(newcontents);
            Contents<K,V> replaceContents = new Contents<K,V>(contents.keys, contents.values,
                    null, newnode);
            current.casContents(contents, replaceContents);
            current = newnode;
        }
        return current;
    }
    
    private void buildFromSortedNonLeaf(int totalCount, K nextKey) {
        int theCount = totalCount, height = 0;                
        while ((theCount & avgLengthMinusOne) == 0) {
            theCount >>>= logAvgLength;
            height++;
        }
        SearchResults[] results = new SearchResults[height + 1];
        Comparable<? super K> key = comparable(nextKey);                
        traverseNonLeaf(key, height, results);
        Node<K,V> right = results[0].node;
        for(int i = 1; i < height; i++) {
            insertOneLevel(nextKey, key, results, right, i);
            right = splitOneLevel(key, results[i]);
        }
        insertOneLevel(nextKey, key, results, right, height);        
    }
    
    /* ---------------- Serialization -------------- */

    /**
     * Save the state of this map to a stream.
     *
     * @serialData The key (Object) and value (Object) for each
     * key-value mapping represented by the map, followed by
     * <tt>null</tt>. The key-value mappings are emitted in key-order
     * (as determined by the Comparator, or by the keys' natural
     * ordering if no Comparator).
     */
    private void writeObject(java.io.ObjectOutputStream s)
        throws java.io.IOException {
        // Write out the Comparator and any hidden stuff
        s.defaultWriteObject();

        // Write out keys and values (alternating)
        SearchResults<K,V> results = findFirst();
        if (results == null) {
            s.writeObject(null);
            return;            
        }
        Node<K,V> node = results.node;
        Contents<K,V> contents = results.contents;
        int index = 0;
        while (node != null) {
            if (index < contents.keys.length) {
                Object okey = contents.keys[index];
                if (okey != PositiveInfinity.INSTANCE) {
                    s.writeObject(okey);
                    if (valueProxy == null) {
                        V value = (V) contents.values[index];                    
                        s.writeObject(value);
                    }
                }
                index++;
            } else {
                node = contents.link;
                if (node != null) contents = node.contents;
                index = 0;
            }
        }
        s.writeObject(null);
    }

    /**
     * Reconstitute the map from a stream.
     */
    private void readObject(final java.io.ObjectInputStream s)
        throws java.io.IOException, ClassNotFoundException {
        // Read in the Comparator and any hidden stuff
        s.defaultReadObject();
        // Reset transients
        initialize();

        while(true) {
            Object k = s.readObject();
            if (k == null) break;
            Object v = (valueProxy == null) ? s.readObject() : valueProxy;
            if (v == null)
                throw new NullPointerException();
            K key = (K) k;
            V val = (V) v;
            put(key, val);
        }        
    }    

    /* ---------------- Comparison utilities -------------- */

    /**
     * Represents a key with a comparator as a Comparable.
     *
     * Because most sorted collections seem to use natural ordering on
     * Comparables (Strings, Integers, etc), most internal methods are
     * geared to use them. This is generally faster than checking
     * per-comparison whether to use comparator or comparable because
     * it doesn't require a (Comparable) cast for each comparison.
     * (Optimizers can only sometimes remove such redundant checks
     * themselves.) When Comparators are used,
     * ComparableUsingComparators are created so that they act in the
     * same way as natural orderings. This penalizes use of
     * Comparators vs Comparables, which seems like the right
     * tradeoff.
     */
    static final class ComparableUsingComparator<K> implements Comparable<K> {
        final K actualKey;
        final Comparator<? super K> cmp;
        ComparableUsingComparator(K key, Comparator<? super K> cmp) {
            this.actualKey = key;
            this.cmp = cmp;
        }
        public int compareTo(K k2) {
            if (k2 == PositiveInfinity.INSTANCE) return(-1);
            return cmp.compare(actualKey, k2);
        }
    }

    /**
     * If using comparator, return a ComparableUsingComparator, else
     * cast key as Comparable, which may cause ClassCastException,
     * which is propagated back to caller.
     */
    private Comparable<? super K> comparable(Object key) throws ClassCastException {
        if (key == null)
            throw new NullPointerException();
        if (comparator != null)
            return new ComparableUsingComparator<K>((K)key, comparator);
        else
            return (Comparable<? super K>)key;
    }
    
    /**
     * Compares using comparator or natural ordering. Used when the
     * ComparableUsingComparator approach doesn't apply.
     */
    int compare(Object o1, Object o2) throws ClassCastException {
        assert((o1 != PositiveInfinity.INSTANCE) || (o2 != PositiveInfinity.INSTANCE));
        if (o1 == PositiveInfinity.INSTANCE) return(1);
        if (o2 == PositiveInfinity.INSTANCE) return(-1);
        K k1 = (K) o1, k2 = (K) o2;
        Comparator<? super K> cmp = comparator;
        if (cmp != null)
            return cmp.compare(k1, k2);
        else
            return ((Comparable<? super K>)k1).compareTo(k2);
    }
    
    static final class PositiveInfinity<K> implements Comparable<K> {
        private static final PositiveInfinity INSTANCE = new PositiveInfinity();
        private PositiveInfinity() {}        
        public int compareTo(K other) { return 1; }
        public String toString() { return "+&#8734;"; }
        public boolean equals(Object other) { return this == other; }
    }
    
    static final class HeadNode<K,V> {
        final Node<K,V> node;
        final int height;
        
        public HeadNode(Node<K,V> node, int height) {
            this.node = node;
            this.height = height;
        }
    }

    static final class Node<K,V> {
        volatile Contents<K,V> contents;
        
        /** Updater for casContents */
        static final AtomicReferenceFieldUpdater<Node, Contents>
            contentsUpdater = AtomicReferenceFieldUpdater.newUpdater
            (Node.class, Contents.class, "contents");
                
        Node(Contents<K,V> contents) {
        	contentsUpdater.set(this, contents);
        }

        boolean casContents(Contents<K,V> expect, Contents<K,V> update) {
        	return(contentsUpdater.compareAndSet(this, expect, update));
        }
        
    }
    
    static final class Contents<K,V> {
        final Object[] keys;
        final Object[] values;
        final Node<K,V>[] children;
        final Node<K,V> link;
        
        Contents(Object[] keys, Object[] values, Node<K,V>[] children, Node<K,V> link) {
            this.keys = keys;
            this.values = values;
            this.children = children;
            this.link = link;
        }                
    }
    
    static final class SearchResults<K,V> {
        final Node<K,V> node;
        final Contents<K,V> contents;
        final int index;
        
        SearchResults(Node<K,V> node, Contents<K,V> contents, int index) {
            this.node = node;
            this.contents = contents;
            this.index = index;
        }        

    }
    
    /* ------ Map API methods ------ */

    /**
     * Returns <tt>true</tt> if this map contains a mapping for the specified
     * key.
     *
     * @param key key whose presence in this map is to be tested
     * @return <tt>true</tt> if this map contains a mapping for the specified key
     * @throws ClassCastException if the specified key cannot be compared
     *         with the keys currently in the map
     * @throws NullPointerException if the specified key is null
     */
    public boolean containsKey(Object key) {
        SearchResults<K,V> results = doGet(key);
        return(results.index >= 0);
    }

    /**
     * Returns the value to which the specified key is mapped,
     * or {@code null} if this map contains no mapping for the key.
     *
     * <p>More formally, if this map contains a mapping from a key
     * {@code k} to a value {@code v} such that {@code key} compares
     * equal to {@code k} according to the map's ordering, then this
     * method returns {@code v}; otherwise it returns {@code null}.
     * (There can be at most one such mapping.)
     *
     * @throws ClassCastException if the specified key cannot be compared
     *         with the keys currently in the map
     * @throws NullPointerException if the specified key is null
     */    
    public V get(Object key) {
        SearchResults<K,V> results = doGet(key);
        if (results.index < 0) return null;
        if (valueProxy == null) return ((V) results.contents.values[results.index]);
        return valueProxy;
    }
    
    /**
     * Associates the specified value with the specified key in this map.
     * If the map previously contained a mapping for the key, the old
     * value is replaced.
     *
     * @param key key with which the specified value is to be associated
     * @param value value to be associated with the specified key
     * @return the previous value associated with the specified key, or
     *         <tt>null</tt> if there was no mapping for the key
     * @throws ClassCastException if the specified key cannot be compared
     *         with the keys currently in the map
     * @throws NullPointerException if the specified key or value is null
     */    
    public V put(K key, V value) {
        if (value == null)
            throw new NullPointerException();
        return doPut(key, value, false);
    }
    
    /**
     * Removes the mapping for the specified key from this map if present.
     *
     * @param  key key for which mapping should be removed
     * @return the previous value associated with the specified key, or
     *         <tt>null</tt> if there was no mapping for the key
     * @throws ClassCastException if the specified key cannot be compared
     *         with the keys currently in the map
     * @throws NullPointerException if the specified key is null
     */    
    public V remove(Object key) {
        return doRemove(key, null);
    }
    
    /**
     * {@inheritDoc}
     *
     * @return the previous value associated with the specified key,
     *         or <tt>null</tt> if there was no mapping for the key
     * @throws ClassCastException if the specified key cannot be compared
     *         with the keys currently in the map
     * @throws NullPointerException if the specified key or value is null
     */
    public V replace(K key, V value) {
        if (value == null)
            throw new NullPointerException();
        return(doReplace(key, null, value));
    }
    
    /**
     * {@inheritDoc}
     *
     * @throws ClassCastException if the specified key cannot be compared
     *         with the keys currently in the map
     * @throws NullPointerException if any of the arguments are null
     */
    public boolean replace(K key, V oldValue, V newValue) {
        if (oldValue == null || newValue == null)
            throw new NullPointerException();
        return(doReplace(key, oldValue, newValue) != null);
    }
    
    /**
     * @throws ClassCastException {@inheritDoc}
     * @throws NullPointerException if {@code fromKey} or {@code toKey} is null
     * @throws IllegalArgumentException {@inheritDoc}
     */
    public ConcurrentNavigableMap<K,V> subMap(K fromKey,
                                              boolean fromInclusive,
                                              K toKey,
                                              boolean toInclusive) {
        if (fromKey == null || toKey == null)
            throw new NullPointerException();
        return new SubMap<K,V>
            (this, fromKey, fromInclusive, toKey, toInclusive, false);
    }

    /**
     * @throws ClassCastException {@inheritDoc}
     * @throws NullPointerException if {@code toKey} is null
     * @throws IllegalArgumentException {@inheritDoc}
     */
    public ConcurrentNavigableMap<K,V> headMap(K toKey,
                                               boolean inclusive) {
        if (toKey == null)
            throw new NullPointerException();
        return new SubMap<K,V>
            (this, null, false, toKey, inclusive, false);
    }

    /**
     * @throws ClassCastException {@inheritDoc}
     * @throws NullPointerException if {@code fromKey} is null
     * @throws IllegalArgumentException {@inheritDoc}
     */
    public ConcurrentNavigableMap<K,V> tailMap(K fromKey,
                                               boolean inclusive) {
        if (fromKey == null)
            throw new NullPointerException();
        return new SubMap<K,V>
            (this, fromKey, inclusive, null, false, false);
    }

    /**
     * @throws ClassCastException {@inheritDoc}
     * @throws NullPointerException if {@code fromKey} or {@code toKey} is null
     * @throws IllegalArgumentException {@inheritDoc}
     */
    public ConcurrentNavigableMap<K,V> subMap(K fromKey, K toKey) {
        return subMap(fromKey, true, toKey, false);
    }

    /**
     * @throws ClassCastException {@inheritDoc}
     * @throws NullPointerException if {@code toKey} is null
     * @throws IllegalArgumentException {@inheritDoc}
     */
    public ConcurrentNavigableMap<K,V> headMap(K toKey) {
        return headMap(toKey, false);
    }

    /**
     * @throws ClassCastException {@inheritDoc}
     * @throws NullPointerException if {@code fromKey} is null
     * @throws IllegalArgumentException {@inheritDoc}
     */
    public ConcurrentNavigableMap<K,V> tailMap(K fromKey) {
        return tailMap(fromKey, true);
    }
    
    /* ------ SortedMap API methods ------ */

    public Comparator<? super K> comparator() {
        return comparator;
    }    
    
    SearchResults<K,V> doGet(Object okey) {
        Comparable<? super K> key = comparable(okey);        
        Node<K,V> node = this.root.node;
        Contents<K,V> contents = node.contents;
        int index = search(contents.keys, key);    
        while(contents.children != null) {
            if (-index - 1 == contents.keys.length) {
                node = contents.link;
            } else if (index < 0) {
                node = contents.children[-index - 1];
            } else {
                node = contents.children[index];
            }
            contents = node.contents;
            index = search(contents.keys, key);            
        }
        while(true) {
            if (-index - 1 == contents.keys.length) {
                node = contents.link;
            } else {
                SearchResults<K,V> results;
                results = new SearchResults<K,V>(node, contents, index);
                return(results);
            }
            contents = node.contents;
            index = search(contents.keys, key);            
        }
    }
    
    V doPut(K kkey, V value, boolean onlyIfAbsent) {
        Comparable<? super K> key = comparable(kkey);
        final int height = randomLevel();
        if (height == 0) {
            SearchResults results = traverseLeaf(key, false);
            return(insertLeafLevel(kkey, key, value, results, onlyIfAbsent));
        } else {
            SearchResults[] results = new SearchResults[height + 1];
            traverseNonLeaf(key, height, results);
            V oldValue = beginInsertOneLevel(kkey, key, value, results, onlyIfAbsent);
            if(oldValue != null) return(oldValue);
            for(int i = 0; i < height; i++) {
                Node<K,V> right = splitOneLevel(key, results[i]);
                insertOneLevel(kkey, key, results, right, i + 1);
            }
            return null;
        }
    }
    
    V doReplace(K kkey, V oldValue, V newValue) {
        Comparable<? super K> key = comparable(kkey);
        SearchResults results = traverseLeaf(key, true);
        while(true) {
            Node<K,V> node = results.node;
            Contents<K,V> contents = results.contents;
            Object[] values = contents.values;
            int index = results.index;
            if (index < 0) {
                return(null);
            } else if (oldValue != null && !values[index].equals(oldValue)) {
                return(null);
            } else {
                V retValue = (V) values[index];
                Object[] newvalues = Arrays.copyOf(values, values.length);
                newvalues[index] = newValue;
                Contents<K,V> update = new Contents<K,V>(contents.keys, newvalues, 
                        null, contents.link);
                if (node.casContents(contents, update)) {
                    return(retValue);
                } else {
                    results = moveForward(node, key);
                }
            }
        }
    }

    /* ---------------- Deletion -------------- */

    /**
     * Main deletion method. 
     *
     * @param okey the key
     * @param value if non-null, the value that must be
     * associated with key
     * @return the node, or null if not found
     */
    V doRemove(Object okey, Object value) {
        Comparable<? super K> key = comparable(okey);
        SearchResults results = traverseLeaf(key, true);
        return(removeFromNode(key, value, results));
    }

    V removeFromNode(Comparable<? super K> key, Object value, SearchResults results) {
        while(true) {
            Node<K,V> node = results.node;
            Contents<K,V> contents = results.contents;
            int index = results.index;
            if (index < 0) {
                return(null);
            } else {
                V v = (valueProxy == null) ? (V) contents.values[index] : valueProxy;
                if (value != null && !value.equals(v)) return null;
                Object[] newkeys = removeSingleItem(contents.keys, index);
                Object[] newvalues = removeSingleItem(contents.values, index);
                Contents<K,V> update = new Contents<K,V>(newkeys, newvalues, null, contents.link);
                if (node.casContents(contents, update)) {
                    return(v);
                } else {
                    results = moveForward(node, key);
                }
            }
        }
    }
    
    /* ---------------- AbstractMap Overrides -------------- */

    /**
     * Compares the specified object with this map for equality.
     * Returns <tt>true</tt> if the given object is also a map and the
     * two maps represent the same mappings.  More formally, two maps
     * <tt>m1</tt> and <tt>m2</tt> represent the same mappings if
     * <tt>m1.entrySet().equals(m2.entrySet())</tt>.  This
     * operation may return misleading results if either map is
     * concurrently modified during execution of this method.
     *
     * @param o object to be compared for equality with this map
     * @return <tt>true</tt> if the specified object is equal to this map
     */
    public boolean equals(Object o) {
        if (o == this)
            return true;
        if (!(o instanceof Map))
            return false;
        Map<?,?> m = (Map<?,?>) o;
        try {
            for (Map.Entry<K,V> e : this.entrySet())
                if (! e.getValue().equals(m.get(e.getKey())))
                    return false;
            for (Map.Entry<?,?> e : m.entrySet()) {
                Object k = e.getKey();
                Object v = e.getValue();
                if (k == null || v == null || !v.equals(get(k)))
                    return false;
            }
            return true;
        } catch (ClassCastException unused) {
            return false;
        } catch (NullPointerException unused) {
            return false;
        }
    }

    /* ------ ConcurrentMap API methods ------ */

    /**
     * {@inheritDoc}
     *
     * @return the previous value associated with the specified key,
     *         or <tt>null</tt> if there was no mapping for the key
     * @throws ClassCastException if the specified key cannot be compared
     *         with the keys currently in the map
     * @throws NullPointerException if the specified key or value is null
     */
    public V putIfAbsent(K key, V value) {
        if (value == null)
            throw new NullPointerException();
        return doPut(key, value, true);
    }
    
    /**
     * {@inheritDoc}
     *
     * @throws ClassCastException if the specified key cannot be compared
     *         with the keys currently in the map
     * @throws NullPointerException if the specified key is null
     */
    public boolean remove(Object key, Object value) {
        if (key == null)
            throw new NullPointerException();
        if (value == null)
            return false;
        return doRemove(key, value) != null;
    }
    
    /**
     * Returns <tt>true</tt> if this map maps one or more keys to the
     * specified value.  This operation requires time linear in the
     * map size.
     *
     * @param value value whose presence in this map is to be tested
     * @return <tt>true</tt> if a mapping to <tt>value</tt> exists;
     *         <tt>false</tt> otherwise
     * @throws NullPointerException if the specified value is null
     */
    public boolean containsValue(Object value) {
        assert(valueProxy == null);
        if (value == null)
            throw new NullPointerException();
        Node<K,V> node = leafHead;
        while(true) {
            Contents<K,V> contents = node.contents;
            Object[] values = contents.values;
            if (values.length == 0) {
                node = contents.link;
                continue;
            }
            for(int i = 0; i < (values.length - 1); i++) {
                if (values[i].equals(value)) return(true);
            }
            node = contents.link;
            if (node == null) return(false);
            else if (values[values.length - 1].equals(value)) return(true);
        }
    }
       
    
    /* ---------------- Iterators -------------- */

    /**
     * Base of iterator classes:
     */
    abstract class Iter<T> implements Iterator<T> {
        /** The state of the iterator. */
        Node<K,V> previousNode, node;
        Contents<K,V> previousContents, contents;
        /** Cache of the next key field to return */
        K nextKey;
        /** Cache of next value field to maintain weak consistency */
        V nextValue;
        /** the index within the state of the iterator */
        int previousIndex, index;

        /** Initializes ascending iterator for entire range. */
        Iter() {
            SearchResults<K,V> results = findFirst();
            if (results != null) {
                node = results.node;
                contents = results.contents;
                nextKey = (K) contents.keys[0];
                nextValue = (valueProxy == null) ? (V) contents.values[0] : valueProxy;
            }
        }

        public final boolean hasNext() {
            return contents != null;
        }

        /** Advances next to higher entry. */
        final void advance() {
            if (contents == null)
                throw new NoSuchElementException();            
            previousNode = node;
            previousContents = contents;
            previousIndex = index++;
            if ((index == contents.keys.length - 1) && 
                    (contents.keys[index] == PositiveInfinity.INSTANCE)) {
                contents = null;
            } else if (index == contents.keys.length) {
                node = contents.link;
                contents = node.contents;
                while(contents.keys.length == 0) {
                    node = contents.link;
                    contents = node.contents;
                }
                if (contents.keys[0] == PositiveInfinity.INSTANCE){
                    contents = null;
                } else {
                    index = 0;
                    nextKey = (K) contents.keys[0];
                    nextValue = (valueProxy == null) ? (V) contents.values[0] : valueProxy;
                }
            } else {
                nextKey = (K) contents.keys[index];
                nextValue = (valueProxy == null) ? (V) contents.values[index] : valueProxy;
            }
        }

        public void remove() {
            if (previousContents == null)
                throw new IllegalStateException();
            K key = (K) previousContents.keys[previousIndex];
            SearchResults<K,V> results = new SearchResults<K,V>(previousNode, previousContents, previousIndex);
            removeFromNode(comparable(key), null, results);
            previousContents = null;
        }

    }    
    
    final class ValueIterator extends Iter<V> {
        public V next() {
            V v = nextValue;
            advance();
            return v;
        }
    }
    
    final class KeyIterator extends Iter<K> {
        public K next() {
            K k = nextKey;
            advance();
            return k;
        }
    }
    
    final class EntryIterator extends Iter<Map.Entry<K,V>> {
        public Map.Entry<K,V> next() {
            K k = nextKey;
            V v = nextValue;
            advance();
            return new AbstractMap.SimpleImmutableEntry<K,V>(k, v);
        }
    }    
    

    // Control values OR'ed as arguments to findNear

    private static final int EQ = 1;
    private static final int LT = 2;
    private static final int GT = 0; // Actually checked as !LT    
    
    /**
     * Utility for ceiling, floor, lower, higher methods.
     * @param kkey the key
     * @param rel the relation -- OR'ed combination of EQ, LT, GT
     * @return nearest node fitting relation, or null if no such
     */
    SearchResults<K,V> findNear(K kkey, int rel) {
        Comparable<? super K> key = comparable(kkey);
        for (;;) {
            SearchResults<K,V> b = findPredecessor(key);
            SearchResults<K,V> n = immediateSuccessor(b);
            for (;;) {
                if (n == null)
                    return ((rel & LT) == 0)? null : b;
                SearchResults<K,V> f = immediateSuccessor(n);
                int c = key.compareTo((K) n.contents.keys[n.index]);
                if ((c == 0 && (rel & EQ) != 0) ||
                    (c <  0 && (rel & LT) == 0))
                    return n;
                if ( c <= 0 && (rel & LT) != 0)
                    return b;
                b = n;
                n = f;
            }
        }
    }    
    
    /**
     * Returns SimpleImmutableEntry for results of findNear.
     * @param key the key
     * @param rel the relation -- OR'ed combination of EQ, LT, GT
     * @return Entry fitting relation, or null if no such
     */
    AbstractMap.SimpleImmutableEntry<K,V> getNear(K key, int rel) {
        SearchResults<K,V> n = findNear(key, rel);
        if (n == null)
            return null;
        Contents<K,V> contents = n.contents;
        int index = n.index;
        K nearkey = (K) contents.keys[index];
        V nearvalue = (valueProxy == null) ? (V) contents.values[index] : valueProxy;
        return(new AbstractMap.SimpleImmutableEntry<K,V>(nearkey, nearvalue));
    }
    
    /**
     * Traverses through the data structure to find the location
     * of the key in the bottom level (zero height) of the tree.
     * @param key   the element to be searched for
     * @return      the {@link SearchResults} results
     */
    private SearchResults<K,V> traverseLeaf(Comparable<? super K> key, boolean cleanup) {
        Node<K,V> node = root.node;
        Contents<K,V> contents = node.contents;
        int index = search(contents.keys, key); 
        K leftBarrier = null;
        while(contents.children != null) {
            if (-index - 1 == contents.keys.length) {
                if (contents.keys.length > 0) {
                    leftBarrier = (K) contents.keys[contents.keys.length - 1];
                }
                node = cleanLink(node, contents).link;
            } else {
                assert(contents.keys.length > 0);
                if (index < 0) index = -index - 1;
                if (cleanup) cleanNode(key, node, contents, index, leftBarrier);
                node = contents.children[index];
                leftBarrier = null;
            }
            contents = node.contents;
            index = search(contents.keys, key);            
        }
        while(true) {
            if (index > -contents.keys.length - 1) {
                return new SearchResults<K,V>(node, contents, index);
            } else {
                node = cleanLink(node, contents).link;
            }
            contents = node.contents;
            index = search(contents.keys, key);
        }
    }    
    
    /**
     * Traverses through the data structure to find the locations
     * of the key in the tree. Store the locations of the key in the
     * storeResults array for heights {target, target - 1, ..., 0}.
     * 
     * @param key           the element to be searched for
     * @param target        the max height for populating the storeResults array
     * @param storeResults  the array of {@link SearchResults} results
     */
    private void traverseNonLeaf(Comparable<? super K> key, int target, 
            SearchResults[] storeResults) {
        HeadNode<K,V> root = this.root;
        if (root.height < target) {
            root = increaseRootHeight(target);
        }
        int height = root.height;
        Node<K,V> node = root.node;
        while(true) {
            Contents<K,V> contents = node.contents;
            int index = search(contents.keys, key);
            if (-index - 1 == contents.keys.length) {
                node = contents.link;
            } else if (height == 0) {
                storeResults[0] = new SearchResults<K,V>(node, contents, index);
                return;
            } else {
                SearchResults<K,V> results = new SearchResults<K,V>(node, contents, index);
                results = goodSamaritanCleanNeighbor(key, results);
                if (height <= target) {
                    storeResults[height] = results;
                }
                if (index < 0) index = -index - 1;
                node = contents.children[index];
                height = height - 1;    
            }
        }
    }    
    
    private Contents<K,V> cleanLink(Node<K,V> node, Contents<K,V> contents) {        
        while(true) {
            Node<K,V> newLink = pushRight(contents.link, null);
            if (newLink == contents.link) return (contents);
            Contents<K,V> update = new Contents<K,V>(contents.keys, 
                    contents.values, contents.children, newLink);
            if (node.casContents(contents, update)) return(update);
            contents = node.contents;
        }
    }
    
    private void cleanNode(Comparable<? super K> key, Node<K,V> node, 
            Contents<K,V> contents, int index, K leftBarrier) {
        while(true) {
        	int length = contents.keys.length;
            if (length == 0) {
                return;
            } else if (length == 1) {
                if(cleanNode1(node, contents, leftBarrier)) return;
            } else if (length == 2) {
                if(cleanNode2(node, contents, leftBarrier)) return;
            } else {
                if(cleanNodeN(node, contents, index, leftBarrier)) return;
            }
            contents = node.contents;
            index = search(contents.keys, key);
            if (-index - 1 == contents.keys.length) return;
            else if (index < 0) index = -index - 1;
        }
    }    
        
    private boolean cleanNode1(Node<K,V> node, Contents<K,V> contents, K leftBarrier) {
    	boolean success = attemptSlideKey(node, contents);
    	if (success) return(true);
    	Object key = contents.keys[0];
    	if (leftBarrier != null && compare(key, leftBarrier) <= 0) {
    		leftBarrier = null;
    	}
        Node<K,V> childNode = contents.children[0];
        Node<K,V> adjustedChild = pushRight(childNode, leftBarrier);
        if (adjustedChild == childNode) return true;
        return shiftChild(node, contents, 0, adjustedChild);
    }
    
    private boolean cleanNode2(Node<K,V> node, Contents<K,V> contents, K leftBarrier) {
    	boolean success = attemptSlideKey(node, contents);
    	if (success) return(true);
    	K key = (K) contents.keys[0];
    	if (leftBarrier != null && compare(key, leftBarrier) <= 0) {
    		leftBarrier = null;
    	}
        Node<K,V> childNode1 = contents.children[0];
        Node<K,V> adjustedChild1 = pushRight(childNode1, leftBarrier);
        leftBarrier = (K) contents.keys[0];
        Node<K,V> childNode2 = contents.children[1];
        Node<K,V> adjustedChild2 = pushRight(childNode2, leftBarrier);
        if ((adjustedChild1 == childNode1) && (adjustedChild2 == childNode2)) return true;  
        return shiftChildren(node, contents, adjustedChild1, adjustedChild2);
    }

    
    private boolean cleanNodeN(Node<K,V> node, Contents<K,V> contents, 
            int index, K leftBarrier) {
    	K key0 = (K) contents.keys[0]; 	
        if (index > 0) {
            leftBarrier = (K) contents.keys[index - 1];
        } else if (leftBarrier != null && compare(key0, leftBarrier) <= 0) {
       		leftBarrier = null;
       	}
        Node<K,V> childNode = contents.children[index];
        Node<K,V> adjustedChild = pushRight(childNode, leftBarrier);
        if (index == 0 || index == contents.children.length - 1) {
            if (adjustedChild == childNode) return true;            
            return shiftChild(node, contents, index, adjustedChild);
        }
        Node<K,V> adjustedNeighbor = pushRight(contents.children[index + 1], 
                (K) contents.keys[index]);
        if (adjustedNeighbor == adjustedChild) {
            return dropChild(node, contents, index, adjustedChild);
        } else if (adjustedChild != childNode) {
            return shiftChild(node, contents, index, adjustedChild);            
        } else {
            return true;
        }
    }
    
    private boolean attemptSlideKey(Node<K,V> node, Contents<K,V> contents) {
        if (contents.link == null) return(false);
    	int length = contents.keys.length;
    	K kkey = (K) contents.keys[length - 1];
    	Node<K,V> child = contents.children[length - 1];
    	Node<K,V> sibling = pushRight(contents.link, null);
    	Contents<K,V> siblingContents = sibling.contents;
    	Node<K,V> nephew = null;
    	if (siblingContents.children.length == 0) {
    	    return(false);
    	} else {
    		nephew = siblingContents.children[0];
    	}
    	if (compare(siblingContents.keys[0], kkey) > 0) {
    		nephew = pushRight(nephew, kkey);
    	} else {
    		nephew = pushRight(nephew, null);
    	}
    	if (nephew != child) return(false);
        Comparable<? super K> key = comparable(kkey);    	
    	boolean success = slideToNeighbor(sibling, siblingContents, kkey, key, child);
    	if(success) deleteSlidedKey(node, contents, key);
    	return(true);
    }

    private static<K,V> boolean slideToNeighbor(Node<K,V> sibling, Contents<K,V> sibContents, 
            K kkey, Comparable<? super K> key, Node<K,V> child) {
    	int index = search(sibContents.keys, key);
    	if (index >= 0) {
    		return(true);
    	} else if (index < -1) {
    		return(false);
    	}
    	Object[] keys = generateNewItems(kkey, sibContents.keys, 0);
    	Node<K,V>[] children = generateNewChildren(child, sibContents.children, 0);
    	Contents<K,V> update = new Contents<K,V>(keys, null, children, sibContents.link);
    	if (sibling.casContents(sibContents, update)) {
    		return(true);
    	} else {
    		return(false);
    	}
    }

    private static<K,V> Contents<K,V> deleteSlidedKey(Node<K,V> node, Contents<K,V> contents, 
            Comparable<? super K> comparable) {
    	int index = search(contents.keys, comparable);
    	if (index < 0) return(contents);
    	Object[] keys = removeSingleItem(contents.keys, index);
    	Node<K,V>[] children = removeSingleChild(contents.children, index);
    	Contents<K,V> update = new Contents<K,V>(keys, null, children, contents.link);
    	if (node.casContents(contents, update)) {
    	    return(update);
    	} else {
    	    return(contents);
    	}
    }    

    
    private static <K,V> boolean dropChild(Node<K,V> node,
            Contents<K,V> contents, int index, Node<K,V> adjustedChild) {
        int length = contents.keys.length;
        Object[] newkeys = new Object[length - 1];
        Node<K,V>[] newchildren = new Node[length - 1];
        for(int i = 0; i < index; i++) {
            newkeys[i] = contents.keys[i];
            newchildren[i] = contents.children[i];
        }
        newchildren[index] = adjustedChild;
        for(int i = index + 1; i < length; i++) {
            newkeys[i - 1] = contents.keys[i];
        }
        for(int i = index + 2; i < length; i++) {
            newchildren[i - 1] = contents.children[i];
        }        
        Contents<K,V> update = new Contents<K,V>(newkeys, 
                null, newchildren, contents.link);
        return node.casContents(contents, update);
    }

    private static <K,V> boolean shiftChild(Node<K,V> node, 
            Contents<K,V> contents, int index, Node<K,V> adjustedChild) {
        Node<K,V>[] newChildren = Arrays.copyOf(contents.children, 
                contents.children.length);
        newChildren[index] = adjustedChild;
        Contents<K,V> update = new Contents<K,V>(contents.keys, 
                null, newChildren, contents.link);
        return node.casContents(contents, update);
    }
    
    private static <K,V> boolean shiftChildren(Node<K,V> node, 
            Contents<K,V> contents, Node<K,V> child1, Node<K,V> child2) {
        Node<K,V>[] newChildren = new Node[2];
        newChildren[0] = child1;
        newChildren[1] = child2;        
        Contents<K,V> update = new Contents<K,V>(contents.keys, 
                null, newChildren, contents.link);
        return node.casContents(contents, update);
    }
    
    private Node<K,V> pushRight(Node<K,V> node, K leftBarrier) {
        while(true) {
            Contents<K,V> contents = node.contents;
            int length = contents.keys.length;
            if (length == 0) {
                node = contents.link;
            } else if (leftBarrier == null || compare(
                    contents.keys[length - 1], leftBarrier) > 0) {
                return node;
            } else {
                node = contents.link;
            }
        }
    }

	private SearchResults goodSamaritanCleanNeighbor(
	        Comparable<? super K> key, SearchResults<K,V> results) {
	    Node<K,V> node = results.node;
	    Contents<K,V> contents = results.contents;
        if (contents.link == null) return(results);
        int length = contents.keys.length;
        K lBarrier = (K) contents.keys[length - 1];
        Node<K,V> child = contents.children[length - 1];
        Node<K,V> sibling = pushRight(contents.link, null);
        Contents<K,V> siblingContents = sibling.contents;
        Node<K,V> nephew = null, adjustedNephew = null;
        if (siblingContents.children.length == 0) {
            contents = cleanLink(node, node.contents);
            int index = search(contents.keys, key);
            return new SearchResults(node, contents, index);
        } else {
            nephew = siblingContents.children[0];
        }
        if (compare(siblingContents.keys[0], lBarrier) > 0) {
            adjustedNephew = pushRight(nephew, lBarrier);
        } else {
            adjustedNephew = pushRight(nephew, null);
        }
        if (nephew != child) {
            if (adjustedNephew != nephew) shiftChild(sibling, siblingContents, 0, adjustedNephew);
        } else {
            Comparable<? super K> compareItem = comparable(lBarrier);
            boolean success = slideToNeighbor(sibling, siblingContents, lBarrier, compareItem, child);
            if(success) {
                contents = deleteSlidedKey(node, contents, compareItem);
                int index = search(contents.keys, key);
                return new SearchResults(node, contents, index);
            }
        }
        return(results);
	}    

	/**
	 * Moves forward along the same level as the input node and
	 * stop after locating the node that either contains or would
	 * contain the key.
	 *  
	 * @param node  the starting node for the search
	 * @param key   the target key
	 * @return      the {@link SearchResults} for the target key
	 */
	private static<K,V> SearchResults<K,V> moveForward(
			Node<K,V> node, Comparable<? super K> key) {
	    while(true) {
	        Contents<K,V> contents = node.contents;
	        int index = search(contents.keys, key);
	        if (index > -contents.keys.length - 1) {
                return new SearchResults<K,V>(node, contents, index);	            
	        } else {
	            node = contents.link;
	        }
	    }
	}

	/**
	 * Splits a linked list level using element x as a pivot element.
	 * The {@link SearchResults} provide a hint as to where x is located.
	 * A split is performed if-and-only-if (a) the node contains the target
	 * key, (b) the node contains at least two elements, and (c) the target
	 * key is not the last element of the node. After the split, the node is
	 * replaced with the new "left" node, which contains x and elements less
	 * than x.  The function returns the "right" node which is created during
	 * the split operation.
	 * 
	 * @param x        the element to use as a pivot
	 * @param results  a hint to locate element x
	 * @return         the new "right" node
	 */
	private Node<K,V> splitOneLevel(Comparable<? super K> x, SearchResults<K,V> results) {
        while(true) {
            Node<K,V> node = results.node;
            Contents<K,V> contents = results.contents;
            int index = results.index;
            int length = contents.keys.length;
            if (index < 0) {
                return(null);
            } else if (length < 2 || index == (length - 1)) {
                return(null);
            }
            Object[] leftkeys = generateLeftItems(contents.keys, index);
            Object[] rightkeys = generateRightItems(contents.keys, index);
            Object[] leftvalues = generateLeftItems(contents.values, index);
            Object[] rightvalues = generateRightItems(contents.values, index);
            Node<K,V>[] leftchildren = generateLeftChildren(contents.children, index);
            Node<K,V>[] rightchildren = generateRightChildren(contents.children, index);
            Node<K,V> right = new Node<K,V>(new Contents<K,V>(
                    rightkeys, rightvalues, rightchildren, contents.link));
            Contents<K,V> left = new Contents<K,V>(leftkeys, leftvalues, leftchildren, right);
            if (node.casContents(contents, left)) {
                return(right);
            } else {
                results = moveForward(node, x);
            }
        }
    }
	
    private V insertLeafLevel(K kkey, 
            Comparable<? super K> key, V value, SearchResults results, boolean onlyIfAbsent) {
        while(true) {
            Node<K,V> node = results.node;
            Contents<K,V> contents = results.contents;
            Object[] keys = contents.keys;
            Object[] values = contents.values;
            int index = results.index;
            if (index >= 0) {
                if (onlyIfAbsent) {
                    return (valueProxy == null) ? ((V) values[index]) : (valueProxy);
                }
                Object[] newvalues = null;
                if (valueProxy == null) {
                    newvalues = Arrays.copyOf(values, values.length);
                    newvalues[index] = value;
                }
                Contents<K,V> update = new Contents<K,V>(keys, 
                        newvalues, null, contents.link);
                if (node.casContents(contents, update)) {
                    return(valueProxy == null ? (V) values[index] : valueProxy);
                } else {
                    results = moveForward(node, key);                    
                }
            } else {
                index = - index - 1;
                assert(index >= 0 && index < keys.length);
                Object[] newkeys = generateNewItems(kkey, keys, index);
                Object[] newvalues = generateNewItems(value, values, index);
                Contents<K,V> update = new Contents<K,V>(newkeys, newvalues, null, contents.link);
                if (node.casContents(contents, update)) {
                    return(null);
                } else {
                    results = moveForward(node, key);
                }
            }
        }        
    }
    
    private V beginInsertOneLevel(K kkey, Comparable<? super K> key, V value,
            SearchResults[] resultsStore, boolean onlyIfAbsent) {
        SearchResults results = resultsStore[0];
        while(true) {
            Node<K,V> node = results.node;
            Contents<K,V> contents = results.contents;
            int index = results.index;
            Object[] keys = contents.keys;
            Object[] values = contents.values;
            if (index >= 0) {
                if (onlyIfAbsent) {
                    return (valueProxy == null) ? ((V) values[index]) : (valueProxy);
                }
                Object[] newvalues = null;
                if (valueProxy == null) {
                    newvalues = Arrays.copyOf(values, values.length);
                    newvalues[index] = value;                    
                }
                Contents<K,V> update = new Contents<K,V>(keys, 
                        newvalues, null, contents.link);
                if (node.casContents(contents, update)) {
                    return((V) values[index]);
                } else {
                    results = moveForward(node, key);
                }
            } else {
                index = - index - 1;
                assert(index >= 0 && index < keys.length);
                Object[] newkeys = generateNewItems(kkey, keys, index);
                Object[] newvalues = generateNewItems(value, values, index);
                Contents<K,V> update = new Contents<K,V>(newkeys, newvalues, null, contents.link);
                if (node.casContents(contents, update)) {
                    SearchResults newResults = new SearchResults<K,V>(node, update, index);
                    resultsStore[0] = newResults;
                    return(null);
                } else {
                    results = moveForward(node, key);
                }
            }
        }
    }
	
    
    private void insertOneLevel(K kkey, Comparable<? super K> key,
            SearchResults[] resultsStore, Node<K,V> child, 
            int target) {
        assert(target > 0);
        if (child == null) return;
        SearchResults results = resultsStore[target];
        while(true) {
            Node<K,V> node = results.node;
            Contents<K,V> contents = results.contents;
            int index = results.index;            
            if (index >= 0) {
                return;
            } else if (index > - contents.keys.length - 1) {
                index = - index - 1;
                assert(index >= 0 && index < contents.keys.length);
                Object[] newkeys = generateNewItems(kkey, contents.keys, index);
                Node<K,V>[] newchildren = generateNewChildren(child, contents.children, index + 1);
                Contents<K,V> update = new Contents<K,V>(newkeys, null, newchildren, contents.link);
                if (node.casContents(contents, update)) {
                    SearchResults newResults = new SearchResults<K,V>(node, update, index);
                    resultsStore[target] = newResults;
                    return;
                } else {
                    results = moveForward(node, key);
                }
            } else {
                assert(index == - contents.keys.length - 1);                
                results = moveForward(node, key);
            }
        }
    }
    
    private static Object[] removeSingleItem(Object[] items, int index) {
        if (items == null) return(null);
        int length = items.length;
        Object[] newitems = new Object[length - 1];
        for(int i = 0; i < index; i++) {
            newitems[i] = items[i];
        }
        for(int i = index + 1; i < length; i++) {
            newitems[i - 1] = items[i];
        }
        return(newitems);
    }
    
    private static <K,V> Node<K,V>[] removeSingleChild(
    		Node<K,V>[] children, int index) {
        int length = children.length;
        Node<K,V>[] newchildren = new Node[length - 1];
        for(int i = 0; i < index; i++) {
        	newchildren[i] = children[i];
        }
        for(int i = index + 1; i < length; i++) {
        	newchildren[i - 1] = children[i];
        }
        return(newchildren);
    }
    
    private static <K> Object[] generateNewItems(
    		K x, Object[] items, int index) {
        if (items == null) return(null);
        int length = items.length;
        Object[] newitems = new Object[length + 1];
        for(int i = 0; i < index; i++) {
            newitems[i] = items[i];
        }
        newitems[index] = x;
        for(int i = index; i < length; i++) {
            newitems[i + 1] = items[i];
        }
        return(newitems);
    }    
    
    private static <K,V> Node<K,V>[] generateNewChildren(
    		Node<K,V> child, Node<K,V>[] children, 
            int index) {
        if (child == null) return(null);
        int length = children.length;
        Node<K,V>[] newchildren = new Node[length + 1];
        for(int i = 0; i < index; i++) {
            newchildren[i] = children[i];
        }
        newchildren[index] = child;
        for(int i = index; i < length; i++) {
            newchildren[i + 1] = children[i];
        }
        return(newchildren);
    }
        
    private static Object[] generateLeftItems(Object[] items, int index) {
        if (items == null) return(null);
        Object[] newitems = new Object[index + 1];
        for(int i = 0; i <= index; i++) {
            newitems[i] = items[i];
        }
        return(newitems);
    }

    private static Object[] generateRightItems(Object[] items, int index) {
        if (items == null) return(null);        
        int length = items.length;
        Object[] newitems = new Object[length - index - 1];
        for(int i = 0, j = index + 1; j < length; i++, j++) {
            newitems[i] = items[j];
        }
        return(newitems);
    }
    
    private static <K,V> Node<K,V>[] generateLeftChildren(
    		Node<K,V>[] children, int index) {
        if (children == null) return(null);
        Node<K,V>[] newchildren = new Node[index + 1];
        for(int i = 0; i <= index; i++) {
            newchildren[i] = children[i];
        }
        return(newchildren);
    }

    private static <K,V> Node<K,V>[] generateRightChildren(
    		Node<K,V>[] children, int index) {
        if (children == null) return(null);
        int length = children.length;
        Node<K,V>[] newchildren  = new Node[length - index - 1];
        for(int i = 0, j = index + 1; j < length; i++, j++) {
            newchildren[i] = children[j];
        }
        return(newchildren);
    }
        
    private HeadNode<K,V> increaseRootHeight(int target) {
        HeadNode<K,V> root = this.root;
        int height = root.height;
        while(height < target) {
            Object[] keys = new Object[1];
            Node<K,V>[] children = new Node[1];
            keys[0] = PositiveInfinity.INSTANCE;            
            children[0] = root.node;
            Contents<K,V> contents = new Contents<K,V>(keys, null, children, null);
            Node<K,V> newNode = new Node<K,V>(contents);
            HeadNode<K,V> update = new HeadNode<K,V>(newNode, height + 1);
            rootUpdater.compareAndSet(this, root, update);
            root = this.root;
            height = root.height;
        }
        return(root);
    }
    
    /* ---------------- Finding and removing first element -------------- */

    /**
     * Specialized variant of findNode to get first valid node.
     * @return SearchResults containing first node and contents,
     *         or null if the tree is empty.
     */
    SearchResults<K,V> findFirst() {
        while(true) {
            Node<K,V> node = this.leafHead;
            Contents<K,V> contents = node.contents;
            if (contents.keys.length == 0) {
                leafHeadUpdater.compareAndSet(this, node, contents.link);
            } else if (contents.keys[0] == PositiveInfinity.INSTANCE) {
                return null;
            } else {
                return new SearchResults<K,V>(node, contents, 0);
            }
        }
    }
    
    /**
     * Removes first entry; returns its snapshot.
     * @return null if empty, else snapshot of first entry
     */
    Map.Entry<K,V> doRemoveFirstEntry() {
        Node<K,V> node = this.leafHead;        
        while(true) {
            Contents<K,V> contents = node.contents;
            if (contents.keys.length == 0) {
                if(leafHeadUpdater.compareAndSet(this, node, contents.link)) {
                    node = contents.link;
                } else {
                    node = this.leafHead;
                }
            } else {
                Object okey = contents.keys[0];
                V value = (valueProxy == null) ? (V) contents.values[0] : valueProxy;
                if (okey == PositiveInfinity.INSTANCE) return null;
                Object[] newkeys = removeSingleItem(contents.keys, 0);
                Object[] newvalues = removeSingleItem(contents.values, 0);
                Contents<K,V> update = new Contents<K,V>(newkeys, newvalues, null, contents.link);
                if (node.casContents(contents, update)) {
                    return(new AbstractMap.SimpleImmutableEntry<K,V>((K) okey, value));
                }
            }
        }
    }
    
    /* ---------------- Finding and removing last element -------------- */

    private SearchResults<K,V> findLastBuildStack(Stack<SearchResults<K,V>> stack) {
        Node<K,V> node = this.root.node;
        Contents<K,V> contents = node.contents;
        while(contents.children != null) {
            if (contents.link != null) {
                node = contents.link;
            } else {
                stack.push(new SearchResults<K,V>(node, contents, 0));
                node = contents.children[contents.children.length - 1];
            }
            contents = node.contents;
        }
        return(doLeafFindLast(node, contents));
    }
    
    private SearchResults<K,V> secondPassFindLast(SearchResults<K,V> initial) {
        Node<K,V> node = initial.node;
        Contents<K,V> contents = initial.contents;
        while(contents.children != null) {
            if (contents.children.length < 2) {
                return null;
            } else {
                node = contents.children[contents.children.length - 2];
                contents = node.contents;
            }
        }
        return(doLeafFindLast(node, contents));
    }
    
    private SearchResults<K,V> findLastLeaves() {
        Node<K,V> node = this.leafHead;
        Contents<K,V> contents = node.contents;
        return(doLeafFindLast(node, contents));
    }

    private SearchResults<K,V> doLeafFindLast(Node<K, V> node, Contents<K, V> contents) {
        Node<K,V> prevNode = null;
        Contents<K,V> prevContents = null;
        while(true) {
            if (contents.link != null) {
                if (contents.keys.length > 0) {
                    prevNode = node;
                    prevContents = contents;
                }
                node = contents.link;                
                contents = node.contents;
            } else if (contents.keys.length == 1) {
                if (prevContents == null) return(null);
                else return(new SearchResults<K,V>(prevNode, prevContents, 
                        prevContents.keys.length - 1));
            } else {
                return(new SearchResults<K,V>(node, contents, contents.keys.length - 2));
            }
        }
    }
    
    /**
     * Specialized version of find to get last valid node.
     * @return last node or null if empty
     */
    SearchResults<K,V> findLast() {
        Stack<SearchResults<K,V>> stack = new Stack<SearchResults<K,V>>();
        SearchResults<K,V> predecessor = findLastBuildStack(stack);
        while(predecessor == null && !stack.isEmpty()) {
           SearchResults<K,V> next = stack.pop();
           predecessor = secondPassFindLast(next);
        }
        if (predecessor == null) return(findLastLeaves());
        return(predecessor);
    }


    /**
     * Returns a key-value mapping associated with the least
     * key in this map, or <tt>null</tt> if the map is empty.
     * The returned entry does <em>not</em> support
     * the <tt>Entry.setValue</tt> method.
     */
    public Map.Entry<K,V> firstEntry() {
        SearchResults<K,V> results = findFirst();
        if (results == null) return null;
        Contents<K,V> contents = results.contents;
        K key = (K) contents.keys[0];
        V value = (valueProxy == null) ? (V) contents.values[0] : valueProxy;
        return new AbstractMap.SimpleImmutableEntry<K,V>(key, value);
    }
    
    /**
     * Returns a key-value mapping associated with the greatest
     * key in this map, or <tt>null</tt> if the map is empty.
     * The returned entry does <em>not</em> support
     * the <tt>Entry.setValue</tt> method.
     */
    public Map.Entry<K,V> lastEntry() {
        SearchResults<K,V> results = findLast();
        if (results == null)
            throw new NoSuchElementException();
        Contents<K,V> contents = results.contents;
        Object okey = contents.keys[0];
        V value = (valueProxy == null) ? (V) contents.values[0] : valueProxy;
        return new AbstractMap.SimpleImmutableEntry<K,V>((K) okey, value);        
    }
    
    /**
     * Removes and returns a key-value mapping associated with
     * the least key in this map, or <tt>null</tt> if the map is empty.
     * The returned entry does <em>not</em> support
     * the <tt>Entry.setValue</tt> method.
     */
    public Map.Entry<K,V> pollFirstEntry() {
        return doRemoveFirstEntry();
    }

    /**
     * Removes and returns a key-value mapping associated with
     * the greatest key in this map, or <tt>null</tt> if the map is empty.
     * The returned entry does <em>not</em> support
     * the <tt>Entry.setValue</tt> method.
     */
    public Map.Entry<K,V> pollLastEntry() {
        while(true) {
            SearchResults<K,V> lastEntry = findLast();
            if (lastEntry == null) return(null);
            Node<K,V> node = lastEntry.node;
            Contents<K,V> contents = lastEntry.contents;
            int index = lastEntry.index;
            K key = (K) contents.keys[index];
            V value = (valueProxy == null) ? (V) contents.values[index] : valueProxy;
            Object[] newkeys = removeSingleItem(contents.keys, index);
            Object[] newvalues = removeSingleItem(contents.values, index);
            Contents<K,V> update = new Contents<K,V>(newkeys, newvalues, null, contents.link);
            if (node.casContents(contents, update)) {
                return(new AbstractMap.SimpleImmutableEntry<K,V>(key, value));
            }
        }
    }
    
    /**
     * @throws NoSuchElementException {@inheritDoc}
     */
    public K firstKey() {
        SearchResults<K,V> results = findFirst();
        if (results == null) throw new NoSuchElementException();
        Contents<K,V> contents = results.contents;
        K key = (K) contents.keys[0];
        return(key);
    }
    
    /**
     * @throws NoSuchElementException {@inheritDoc}
     */
    public K lastKey() {
        SearchResults<K,V> results = findLast();
        if (results == null)
            throw new NoSuchElementException();
        return (K) results.contents.keys[results.index];
    }
    
    /* ---------------- Traversal -------------- */
    
    SearchResults<K,V> immediateSuccessor(SearchResults<K,V> start) {
        if (start == null) {
            return(findFirst());
        }
        Node<K,V> node = start.node;
        Contents<K,V> contents = start.contents;
        int index = start.index + 1;
        while(true) {
            if (contents.keys.length == 0) {
                node = contents.link;
            } else if (index == contents.keys.length) {
                node = contents.link;
            } else if (contents.keys[index] == PositiveInfinity.INSTANCE) {
                return null;
            } else {
                return new SearchResults<K,V>(node, contents, index);
            }
            if (node == null) return null;
            contents = node.contents;
            index = 0;            
        }
    }    
        
    SearchResults<K,V> doFindPredecessor(Comparable<? super K> key,
            SearchResults<K,V> start, Stack<SearchResults<K,V>> stack) {
        Node<K,V> node = start.node;
        Contents<K,V> contents = start.contents;
        int index = start.index;
        while(contents.children != null) {
            if (-index - 1 == contents.keys.length) {
                node = contents.link;
            } else {
                if (index < 0) index = -index - 1;
                if (stack != null) {
                    SearchResults<K,V> entry;
                    entry = new SearchResults<K,V>(node, contents, index);
                    stack.push(entry);
                }
                node = contents.children[index];
            }
            contents = node.contents;
            index = search(contents.keys, key);
        }
        SearchResults<K,V> leaf = 
            new SearchResults<K,V>(node, contents, index);
        return(leafFindPredecessor(key, leaf));
    }

    SearchResults<K,V> leafFindPredecessor(Comparable<? super K> key, SearchResults<K,V> start) {
        Node<K,V> node = start.node;
        Contents<K,V> contents = start.contents;
        int index = start.index;
        Node<K,V> prevNode = null;
        Contents<K,V> prevContents = null;
        while(true) {
            if (-index - 1 == contents.keys.length) {
                if (contents.keys.length > 0) {
                    prevNode = node;
                    prevContents = contents;
                }
                node = contents.link;
            } else if (index == 0 || index == -1) {
                if (prevNode == null) return null;
                return new SearchResults<K,V>(prevNode, prevContents, 
                        prevContents.keys.length - 1);
            } else if (index > 0) {
                return(new SearchResults<K,V>(node, contents, index - 1));
            } else {
                return(new SearchResults<K,V>(node, contents, -index - 2));
            }
            contents = node.contents;
            index = search(contents.keys, key);
        }
    }
    
    /**
     * Returns the search results of a key strictly less than given key,
     * or null if there is no such node.
     * @param key the key
     * @return a predecessor of key
     */
    SearchResults<K,V> findPredecessor(Comparable<? super K> key) {
        if (key == null)
            throw new NullPointerException(); // don't postpone errors
        Stack<SearchResults<K,V>> stack = new Stack<SearchResults<K,V>>();
        Node<K,V> node = this.root.node;
        Contents<K,V> contents = node.contents;
        int index = search(contents.keys, key);
        SearchResults<K,V> predecessor = doFindPredecessor(key, 
                new SearchResults<K,V>(node, contents, index), stack);
        while((predecessor == null) && !stack.isEmpty()) {
            SearchResults<K,V> stackSearch = stack.pop();
            node = stackSearch.node;
            contents = stackSearch.contents;
            index = stackSearch.index;
            assert(index >= 0);
            if (index == 0) continue;
            predecessor = doFindPredecessor(key, 
                    new SearchResults<K,V>(node, contents, index - 1), 
                    null);
        }
        if (predecessor == null) {
            node = this.leafHead;
            contents = node.contents;
            index = search(contents.keys, key);
            predecessor = new SearchResults<K,V>(node, contents, index);
            return leafFindPredecessor(key, predecessor);
        }
        return(predecessor);
    }    
    
    /* ---------------- Relational operations -------------- */

    /**
     * Returns a key-value mapping associated with the greatest key
     * strictly less than the given key, or <tt>null</tt> if there is
     * no such key. The returned entry does <em>not</em> support the
     * <tt>Entry.setValue</tt> method.
     *
     * @throws ClassCastException {@inheritDoc}
     * @throws NullPointerException if the specified key is null
     */
    public Map.Entry<K,V> lowerEntry(K key) {
        return getNear(key, LT);
    }

    /**
     * @throws ClassCastException {@inheritDoc}
     * @throws NullPointerException if the specified key is null
     */
    public K lowerKey(K key) {
        SearchResults<K,V> n = findNear(key, LT);
        return (n == null)? null : (K) n.contents.keys[n.index];
    }

    /**
     * Returns a key-value mapping associated with the greatest key
     * less than or equal to the given key, or <tt>null</tt> if there
     * is no such key. The returned entry does <em>not</em> support
     * the <tt>Entry.setValue</tt> method.
     *
     * @param key the key
     * @throws ClassCastException {@inheritDoc}
     * @throws NullPointerException if the specified key is null
     */
    public Map.Entry<K,V> floorEntry(K key) {
        return getNear(key, LT|EQ);
    }

    /**
     * @param key the key
     * @throws ClassCastException {@inheritDoc}
     * @throws NullPointerException if the specified key is null
     */
    public K floorKey(K key) {
        SearchResults<K,V> n = findNear(key, LT|EQ);
        return (n == null)? null : (K) n.contents.keys[n.index];
    }

    /**
     * Returns a key-value mapping associated with the least key
     * greater than or equal to the given key, or <tt>null</tt> if
     * there is no such entry. The returned entry does <em>not</em>
     * support the <tt>Entry.setValue</tt> method.
     *
     * @throws ClassCastException {@inheritDoc}
     * @throws NullPointerException if the specified key is null
     */
    public Map.Entry<K,V> ceilingEntry(K key) {
        return getNear(key, GT|EQ);
    }

    /**
     * @throws ClassCastException {@inheritDoc}
     * @throws NullPointerException if the specified key is null
     */
    public K ceilingKey(K key) {
        SearchResults<K,V> n = findNear(key, GT|EQ);
        return (n == null)? null : (K) n.contents.keys[n.index];
    }

    /**
     * Returns a key-value mapping associated with the least key
     * strictly greater than the given key, or <tt>null</tt> if there
     * is no such key. The returned entry does <em>not</em> support
     * the <tt>Entry.setValue</tt> method.
     *
     * @param key the key
     * @throws ClassCastException {@inheritDoc}
     * @throws NullPointerException if the specified key is null
     */
    public Map.Entry<K,V> higherEntry(K key) {
        return getNear(key, GT);
    }

    /**
     * @param key the key
     * @throws ClassCastException {@inheritDoc}
     * @throws NullPointerException if the specified key is null
     */
    public K higherKey(K key) {
        SearchResults<K,V> n = findNear(key, GT);
        return (n == null)? null : (K) n.contents.keys[n.index];
    }
    
    /**
     * Returns <tt>true</tt> if this map contains no key-value mappings.
     * @return <tt>true</tt> if this map contains no key-value mappings
     */
    public boolean isEmpty() {
        SearchResults<K,V> results = findFirst();
        return (results == null);
    }
    
    public int size() {
        Node<K,V> node = this.leafHead;
        Contents<K,V> contents = node.contents;
        while(contents.keys.length == 0) {
            if(leafHeadUpdater.compareAndSet(this, node, contents.link)) {
                node = contents.link;
            } else {
                node = this.leafHead;
            }
            contents = node.contents;
        }
        int count = 0;
        while (node != null) {
            contents = node.contents;
            count += contents.keys.length;
            node = contents.link;
        }
        return(count - 1); // ignore positive infinity
    }
    
    /**
     * Removes all of the mappings from this map.
     */
    public void clear() {
        initialize();
    }    
    
    /**
     * Returns a {@link NavigableSet} view of the keys contained in this map.
     * The set's iterator returns the keys in ascending order.
     * The set is backed by the map, so changes to the map are
     * reflected in the set, and vice-versa.  The set supports element
     * removal, which removes the corresponding mapping from the map,
     * via the {@code Iterator.remove}, {@code Set.remove},
     * {@code removeAll}, {@code retainAll}, and {@code clear}
     * operations.  It does not support the {@code add} or {@code addAll}
     * operations.
     *
     * <p>The view's {@code iterator} is a "weakly consistent" iterator
     * that will never throw {@link ConcurrentModificationException},
     * and guarantees to traverse elements as they existed upon
     * construction of the iterator, and may (but is not guaranteed to)
     * reflect any modifications subsequent to construction.
     *
     * <p>This method is equivalent to method {@code navigableKeySet}.
     *
     * @return a navigable set view of the keys in this map
     */
     public NavigableSet<K> keySet() {
        KeySet ks = keySet;
        return (ks != null) ? ks : (keySet = new KeySet(this));
    }

    public NavigableSet<K> navigableKeySet() {
        KeySet ks = keySet;
        return (ks != null) ? ks : (keySet = new KeySet(this));
    }

    /**
     * Returns a {@link Collection} view of the values contained in this map.
     * The collection's iterator returns the values in ascending order
     * of the corresponding keys.
     * The collection is backed by the map, so changes to the map are
     * reflected in the collection, and vice-versa.  The collection
     * supports element removal, which removes the corresponding
     * mapping from the map, via the <tt>Iterator.remove</tt>,
     * <tt>Collection.remove</tt>, <tt>removeAll</tt>,
     * <tt>retainAll</tt> and <tt>clear</tt> operations.  It does not
     * support the <tt>add</tt> or <tt>addAll</tt> operations.
     *
     * <p>The view's <tt>iterator</tt> is a "weakly consistent" iterator
     * that will never throw {@link ConcurrentModificationException},
     * and guarantees to traverse elements as they existed upon
     * construction of the iterator, and may (but is not guaranteed to)
     * reflect any modifications subsequent to construction.
     */
    public Collection<V> values() {
        Values vs = valuesCollection;
        return (vs != null) ? vs : (valuesCollection = new Values(this));
    }

    /**
     * Returns a {@link Set} view of the mappings contained in this map.
     * The set's iterator returns the entries in ascending key order.
     * The set is backed by the map, so changes to the map are
     * reflected in the set, and vice-versa.  The set supports element
     * removal, which removes the corresponding mapping from the map,
     * via the <tt>Iterator.remove</tt>, <tt>Set.remove</tt>,
     * <tt>removeAll</tt>, <tt>retainAll</tt> and <tt>clear</tt>
     * operations.  It does not support the <tt>add</tt> or
     * <tt>addAll</tt> operations.
     *
     * <p>The view's <tt>iterator</tt> is a "weakly consistent" iterator
     * that will never throw {@link ConcurrentModificationException},
     * and guarantees to traverse elements as they existed upon
     * construction of the iterator, and may (but is not guaranteed to)
     * reflect any modifications subsequent to construction.
     *
     * <p>The <tt>Map.Entry</tt> elements returned by
     * <tt>iterator.next()</tt> do <em>not</em> support the
     * <tt>setValue</tt> operation.
     *
     * @return a set view of the mappings contained in this map,
     *         sorted in ascending key order
     */
    public Set<Map.Entry<K,V>> entrySet() {
        EntrySet es = entrySet;
        return (es != null) ? es : (entrySet = new EntrySet(this));
    }

    public ConcurrentNavigableMap<K,V> descendingMap() {
        ConcurrentNavigableMap<K,V> dm = descendingMap;
        return (dm != null) ? dm : (descendingMap = new SubMap<K,V>
                                    (this, null, false, null, false, true));
    }

    public NavigableSet<K> descendingKeySet() {
        return descendingMap().navigableKeySet();
    }    
    
    // Factory methods for iterators needed by ConcurrentSkipTreeSet etc

    Iterator<K> keyIterator() {
        return new KeyIterator();
    }

    Iterator<V> valueIterator() {
        return new ValueIterator();
    }

    Iterator<Map.Entry<K,V>> entryIterator() {
        return new EntryIterator();
    }    
    
    private static<K> int search(Object[] a, Comparable<? super K> key) {
        int low = 0;
        int high = a.length - 1;
        
        if (low > high) return(-1);
        if (a[high] == PositiveInfinity.INSTANCE) high--;

        while (low <= high) {
            int mid = (low + high) >>> 1;
            K midVal = (K) a[mid];
            int cmp = key.compareTo(midVal);

            if (cmp > 0)
                low = mid + 1;
            else if (cmp < 0)
                high = mid - 1;
            else
                return mid; // key found
        }
        
        return -(low + 1);  // key not found.
    }
    
    /**
     * Returns a random level for inserting a new node.
     * Hardwired to k=1, p=0.03125, max is (MAX_LEVEL - 1)
     */
    int randomLevel() {
        int x = randomSeed;
        x ^= x << 13;
        x ^= x >>> 17;
        randomSeed = x ^= x << 5;
        int level = 1;
        while ((x & avgLengthMinusOne) == 0) {
            if ((level % 6) == 0) {
                x = randomSeed;
                x ^= x << 13;
                x ^= x >>> 17;
                randomSeed = x ^= x << 5;
            } else {
                x >>>= logAvgLength;
            }
            level++;
        }
        return (level - 1);
    }
    
    static final <E> List<E> toList(Collection<E> c) {
        // Using size() here would be a pessimization.
        List<E> list = new ArrayList<E>();
        for (E e : c)
            list.add(e);
        return list;
        }

        static final class KeySet<E> extends AbstractSet<E> implements NavigableSet<E> {
            private final ConcurrentNavigableMap<E,Object> m;
            KeySet(ConcurrentNavigableMap<E,Object> map) { m = map; }
            public int size() { return m.size(); }
            public boolean isEmpty() { return m.isEmpty(); }
            public boolean contains(Object o) { return m.containsKey(o); }
            public boolean remove(Object o) { return m.remove(o) != null; }
            public void clear() { m.clear(); }
            public E lower(E e) { return m.lowerKey(e); }
            public E floor(E e) { return m.floorKey(e); }
            public E ceiling(E e) { return m.ceilingKey(e); }
            public E higher(E e) { return m.higherKey(e); }
            public Comparator<? super E> comparator() { return m.comparator(); }
            public E first() { return m.firstKey(); }
            public E last() { return m.lastKey(); }
            public E pollFirst() {
                Map.Entry<E,Object> e = m.pollFirstEntry();
                return e == null? null : e.getKey();
            }
            public E pollLast() {
                Map.Entry<E,Object> e = m.pollLastEntry();
                return e == null? null : e.getKey();
            }
            public Iterator<E> iterator() {
                if (m instanceof ConcurrentSkipTreeMap)
                    return ((ConcurrentSkipTreeMap<E,Object>)m).keyIterator();
                else
                    return ((ConcurrentSkipTreeMap.SubMap<E,Object>)m).keyIterator();
            }
            public boolean equals(Object o) {
                if (o == this)
                    return true;
                if (!(o instanceof Set))
                    return false;
                Collection<?> c = (Collection<?>) o;
                try {
                    return containsAll(c) && c.containsAll(this);
                } catch (ClassCastException unused)   {
                    return false;
                } catch (NullPointerException unused) {
                    return false;
                }
            }
        public Object[] toArray()     { return toList(this).toArray();  }
        public <T> T[] toArray(T[] a) { return toList(this).toArray(a); }
            public Iterator<E> descendingIterator() {
                return descendingSet().iterator();
            }
            public NavigableSet<E> subSet(E fromElement,
                                          boolean fromInclusive,
                                          E toElement,
                                          boolean toInclusive) {
                return new ConcurrentSkipTreeSet<E>
                (m.subMap(fromElement, fromInclusive,
                          toElement,   toInclusive));
            }
            public NavigableSet<E> headSet(E toElement, boolean inclusive) {
                return new ConcurrentSkipTreeSet<E>(m.headMap(toElement, inclusive));
            }
            public NavigableSet<E> tailSet(E fromElement, boolean inclusive) {
                return new ConcurrentSkipTreeSet<E>(m.tailMap(fromElement, inclusive));
            }
            public NavigableSet<E> subSet(E fromElement, E toElement) {
                return subSet(fromElement, true, toElement, false);
            }
            public NavigableSet<E> headSet(E toElement) {
                return headSet(toElement, false);
            }
            public NavigableSet<E> tailSet(E fromElement) {
                return tailSet(fromElement, true);
            }
            public NavigableSet<E> descendingSet() {
                return new ConcurrentSkipTreeSet(m.descendingMap());
            }
        }

        static final class Values<E> extends AbstractCollection<E> {
            private final ConcurrentNavigableMap<Object, E> m;
            Values(ConcurrentNavigableMap<Object, E> map) {
                m = map;
            }
            public Iterator<E> iterator() {
                if (m instanceof ConcurrentSkipTreeMap)
                    return ((ConcurrentSkipTreeMap<Object,E>)m).valueIterator();
                else
                    return ((SubMap<Object,E>)m).valueIterator();
            }
            public boolean isEmpty() {
                return m.isEmpty();
            }
            public int size() {
                return m.size();
            }
            public boolean contains(Object o) {
                return m.containsValue(o);
            }
            public void clear() {
                m.clear();
            }
        public Object[] toArray()     { return toList(this).toArray();  }
        public <T> T[] toArray(T[] a) { return toList(this).toArray(a); }
        }

        static final class EntrySet<K1,V1> extends AbstractSet<Map.Entry<K1,V1>> {
            private final ConcurrentNavigableMap<K1, V1> m;
            EntrySet(ConcurrentNavigableMap<K1, V1> map) {
                m = map;
            }

            public Iterator<Map.Entry<K1,V1>> iterator() {
                if (m instanceof ConcurrentSkipTreeMap)
                    return ((ConcurrentSkipTreeMap<K1,V1>)m).entryIterator();
                else
                    return ((SubMap<K1,V1>)m).entryIterator();
            }

            public boolean contains(Object o) {
                if (!(o instanceof Map.Entry))
                    return false;
                Map.Entry<K1,V1> e = (Map.Entry<K1,V1>)o;
                V1 v = m.get(e.getKey());
                return v != null && v.equals(e.getValue());
            }
            public boolean remove(Object o) {
                if (!(o instanceof Map.Entry))
                    return false;
                Map.Entry<K1,V1> e = (Map.Entry<K1,V1>)o;
                return m.remove(e.getKey(),
                                e.getValue());
            }
            public boolean isEmpty() {
                return m.isEmpty();
            }
            public int size() {
                return m.size();
            }
            public void clear() {
                m.clear();
            }
            public boolean equals(Object o) {
                if (o == this)
                    return true;
                if (!(o instanceof Set))
                    return false;
                Collection<?> c = (Collection<?>) o;
                try {
                    return containsAll(c) && c.containsAll(this);
                } catch (ClassCastException unused)   {
                    return false;
                } catch (NullPointerException unused) {
                    return false;
                }
            }
        public Object[] toArray()     { return toList(this).toArray();  }
        public <T> T[] toArray(T[] a) { return toList(this).toArray(a); }
        }
    
    
    /**
     * Submaps returned by {@link ConcurrentSkipListMap} submap operations
     * represent a subrange of mappings of their underlying
     * maps. Instances of this class support all methods of their
     * underlying maps, differing in that mappings outside their range are
     * ignored, and attempts to add mappings outside their ranges result
     * in {@link IllegalArgumentException}.  Instances of this class are
     * constructed only using the <tt>subMap</tt>, <tt>headMap</tt>, and
     * <tt>tailMap</tt> methods of their underlying maps.
     *
     * @serial include
     */
    static final class SubMap<K,V> extends AbstractMap<K,V>
        implements ConcurrentNavigableMap<K,V>, Cloneable,
                   java.io.Serializable {
        private static final long serialVersionUID = -7647078645895051609L;

        /** Underlying map */
        private final ConcurrentSkipTreeMap<K,V> m;
        /** lower bound key, or null if from start */
        private final K lo;
        /** upper bound key, or null if to end */
        private final K hi;
        /** inclusion flag for lo */
        private final boolean loInclusive;
        /** inclusion flag for hi */
        private final boolean hiInclusive;
        /** direction */
        private final boolean isDescending;

        // Lazily initialized view holders
        private transient KeySet<K> keySetView;
        private transient Set<Map.Entry<K,V>> entrySetView;
        private transient Collection<V> valuesView;

        /**
         * Creates a new submap, initializing all fields
         */
        SubMap(ConcurrentSkipTreeMap<K,V> map,
               K fromKey, boolean fromInclusive,
               K toKey, boolean toInclusive,
               boolean isDescending) {
            if (fromKey != null && toKey != null &&
                map.compare(fromKey, toKey) > 0)
                throw new IllegalArgumentException("inconsistent range");
            this.m = map;
            this.lo = fromKey;
            this.hi = toKey;
            this.loInclusive = fromInclusive;
            this.hiInclusive = toInclusive;
            this.isDescending = isDescending;
        }

        /* ----------------  Utilities -------------- */

        private boolean tooLow(K key) {
            if (lo != null) {
                int c = m.compare(key, lo);
                if (c < 0 || (c == 0 && !loInclusive))
                    return true;
            }
            return false;
        }

        private boolean tooHigh(K key) {
            if (hi != null) {
                int c = m.compare(key, hi);
                if (c > 0 || (c == 0 && !hiInclusive))
                    return true;
            }
            return false;
        }

        private boolean inBounds(K key) {
            return !tooLow(key) && !tooHigh(key);
        }

        private void checkKeyBounds(K key) throws IllegalArgumentException {
            if (key == null)
                throw new NullPointerException();
            if (!inBounds(key))
                throw new IllegalArgumentException("key out of range");
        }

        /**
         * Returns true if node key is less than upper bound of range
         */
        private boolean isBeforeEnd(SearchResults<K,V> n) {
            if (n == null)
                return false;
            if (hi == null)
                return true;
            K k = (K) n.contents.keys[n.index];
            if (k == null) // pass by markers and headers
                return true;
            int c = m.compare(k, hi);
            if (c > 0 || (c == 0 && !hiInclusive))
                return false;
            return true;
        }

        /**
         * Returns lowest node. This node might not be in range, so
         * most usages need to check bounds
         */
        private SearchResults<K,V> loNode() {
            if (lo == null)
                return m.findFirst();
            else if (loInclusive)
                return m.findNear(lo, m.GT|m.EQ);
            else
                return m.findNear(lo, m.GT);
        }

        /**
         * Returns highest node. This node might not be in range, so
         * most usages need to check bounds
         */
        private SearchResults<K,V> hiNode() {
            if (hi == null)
                return m.findLast();
            else if (hiInclusive)
                return m.findNear(hi, m.LT|m.EQ);
            else
                return m.findNear(hi, m.LT);
        }

        /**
         * Returns lowest absolute key (ignoring directonality)
         */
        private K lowestKey() {
            SearchResults<K,V> n = loNode();
            if (isBeforeEnd(n))
                return (K) n.contents.keys[n.index];
            else
                throw new NoSuchElementException();
        }

        /**
         * Returns highest absolute key (ignoring directonality)
         */
        private K highestKey() {
            SearchResults<K,V> n = hiNode();
            if (n != null) {
                K last = (K) n.contents.keys[n.index];
                if (inBounds(last))
                    return last;
            }
            throw new NoSuchElementException();
        }

        private Map.Entry<K,V> lowestEntry() {
            SearchResults<K,V> n = loNode();
            if (!isBeforeEnd(n))
                return null;
            K k = (K) n.contents.keys[n.index];
            V v = (m.valueProxy == null) ? (V) n.contents.values[n.index] : m.valueProxy;
            return new AbstractMap.SimpleImmutableEntry<K,V>(k, v);                
        }

        private Map.Entry<K,V> highestEntry() {
            SearchResults<K,V> n = hiNode();
            if (n == null)
                return null;
            K k = (K) n.contents.keys[n.index];            
            if(!inBounds(k))
                return null;
            V v = (m.valueProxy == null) ? (V) n.contents.values[n.index] : m.valueProxy;
            return new AbstractMap.SimpleImmutableEntry<K,V>(k, v);            
        }

        private Map.Entry<K,V> removeLowest() {
            for (;;) {
                SearchResults<K,V> n = loNode();
                if (n == null) return null;
                K k = (K) n.contents.keys[n.index];
                if (!inBounds(k)) return null;
                V v = m.doRemove(k, null);
                if (v != null)
                    return new AbstractMap.SimpleImmutableEntry<K,V>(k, v);
            }
        }

        private Map.Entry<K,V> removeHighest() {
            for (;;) {
                SearchResults<K,V> n = hiNode();
                if (n == null)
                    return null;
                K k = (K) n.contents.keys[n.index];
                if (!inBounds(k))
                    return null;
                V v = m.doRemove(k, null);
                if (v != null)
                    return new AbstractMap.SimpleImmutableEntry<K,V>(k, v);
            }
        }

        /**
         * Submap version of ConcurrentSkipListMap.getNearEntry
         */
        private Map.Entry<K,V> getNearEntry(K key, int rel) {
            if (isDescending) { // adjust relation for direction
                if ((rel & m.LT) == 0)
                    rel |= m.LT;
                else
                    rel &= ~m.LT;
            }
            if (tooLow(key))
                return ((rel & m.LT) != 0)? null : lowestEntry();
            if (tooHigh(key))
                return ((rel & m.LT) != 0)? highestEntry() : null;
            SearchResults<K,V> n = m.findNear(key, rel);
            if (n == null) return null;
            K k = (K) n.contents.keys[n.index];                
            if (!inBounds(k)) return null;
            V v = (m.valueProxy == null) ? (V) n.contents.values[n.index] : m.valueProxy;
            return new AbstractMap.SimpleImmutableEntry<K,V>(k, v);
        }

        // Almost the same as getNearEntry, except for keys
        private K getNearKey(K key, int rel) {
            if (isDescending) { // adjust relation for direction
                if ((rel & m.LT) == 0)
                    rel |= m.LT;
                else
                    rel &= ~m.LT;
            }
            if (tooLow(key)) {
                if ((rel & m.LT) == 0) {
                    SearchResults<K,V> n = loNode();
                    if (isBeforeEnd(n)) 
                        return (K) n.contents.keys[n.index];
                }
                return null;
            }
            if (tooHigh(key)) {
                if ((rel & m.LT) != 0) {
                    SearchResults<K,V> n = hiNode();
                    if (n != null) {
                        K last = (K) n.contents.keys[n.index];                
                        if (inBounds(last))
                            return last;
                    }
                }
                return null;
            }
            SearchResults<K,V> n = m.findNear(key, rel);
            if (n == null) return null;
            K k = (K) n.contents.keys[n.index];
            if (!inBounds(k)) return null;
            return k;
        }

        /* ----------------  Map API methods -------------- */

        public boolean containsKey(Object key) {
            if (key == null) throw new NullPointerException();
            K k = (K)key;
            return inBounds(k) && m.containsKey(k);
        }

        public V get(Object key) {
            if (key == null) throw new NullPointerException();
            K k = (K)key;
            return ((!inBounds(k)) ? null : m.get(k));
        }

        public V put(K key, V value) {
            checkKeyBounds(key);
            return m.put(key, value);
        }

        public V remove(Object key) {
            K k = (K)key;
            return (!inBounds(k))? null : m.remove(k);
        }

        public int size() {
            long count = 0;
            for (SearchResults<K,V> n = loNode();
                 isBeforeEnd(n); n = m.immediateSuccessor(n)) {
                    ++count;
            }
            return count >= Integer.MAX_VALUE? Integer.MAX_VALUE : (int)count;
        }

        public boolean isEmpty() {
            return !isBeforeEnd(loNode());
        }

        public boolean containsValue(Object value) {
            assert(m.valueProxy == null);
            if (value == null)
                throw new NullPointerException();
            for (SearchResults<K,V> n = loNode();
                 isBeforeEnd(n);
                 n = m.immediateSuccessor(n)) {
                V v = (V) n.contents.values[n.index];
                if (value.equals(v))
                    return true;
            }
            return false;
        }

        public void clear() {
            for (SearchResults<K,V> n = loNode();
                 isBeforeEnd(n);
                 n = m.immediateSuccessor(n)) {
                K key = (K) n.contents.keys[n.index];
                m.remove(key);
            }
        }

        /* ----------------  ConcurrentMap API methods -------------- */

        public V putIfAbsent(K key, V value) {
            checkKeyBounds(key);
            return m.putIfAbsent(key, value);
        }

        public boolean remove(Object key, Object value) {
            K k = (K)key;
            return inBounds(k) && m.remove(k, value);
        }

        public boolean replace(K key, V oldValue, V newValue) {
            checkKeyBounds(key);
            return m.replace(key, oldValue, newValue);
        }

        public V replace(K key, V value) {
            checkKeyBounds(key);
            return m.replace(key, value);
        }

        /* ----------------  SortedMap API methods -------------- */

        public Comparator<? super K> comparator() {
            Comparator<? super K> cmp = m.comparator();
        if (isDescending)
        return Collections.reverseOrder(cmp);
        else
        return cmp;
        }

        /**
         * Utility to create submaps, where given bounds override
         * unbounded(null) ones and/or are checked against bounded ones.
         */
        private SubMap<K,V> newSubMap(K fromKey,
                                      boolean fromInclusive,
                                      K toKey,
                                      boolean toInclusive) {
            if (isDescending) { // flip senses
                K tk = fromKey;
                fromKey = toKey;
                toKey = tk;
                boolean ti = fromInclusive;
                fromInclusive = toInclusive;
                toInclusive = ti;
            }
            if (lo != null) {
                if (fromKey == null) {
                    fromKey = lo;
                    fromInclusive = loInclusive;
                }
                else {
                    int c = m.compare(fromKey, lo);
                    if (c < 0 || (c == 0 && !loInclusive && fromInclusive))
                        throw new IllegalArgumentException("key out of range");
                }
            }
            if (hi != null) {
                if (toKey == null) {
                    toKey = hi;
                    toInclusive = hiInclusive;
                }
                else {
                    int c = m.compare(toKey, hi);
                    if (c > 0 || (c == 0 && !hiInclusive && toInclusive))
                        throw new IllegalArgumentException("key out of range");
                }
            }
            return new SubMap<K,V>(m, fromKey, fromInclusive,
                                   toKey, toInclusive, isDescending);
        }

        public SubMap<K,V> subMap(K fromKey,
                                  boolean fromInclusive,
                                  K toKey,
                                  boolean toInclusive) {
            if (fromKey == null || toKey == null)
                throw new NullPointerException();
            return newSubMap(fromKey, fromInclusive, toKey, toInclusive);
        }

        public SubMap<K,V> headMap(K toKey,
                                   boolean inclusive) {
            if (toKey == null)
                throw new NullPointerException();
            return newSubMap(null, false, toKey, inclusive);
        }

        public SubMap<K,V> tailMap(K fromKey,
                                   boolean inclusive) {
            if (fromKey == null)
                throw new NullPointerException();
            return newSubMap(fromKey, inclusive, null, false);
        }

        public SubMap<K,V> subMap(K fromKey, K toKey) {
            return subMap(fromKey, true, toKey, false);
        }

        public SubMap<K,V> headMap(K toKey) {
            return headMap(toKey, false);
        }

        public SubMap<K,V> tailMap(K fromKey) {
            return tailMap(fromKey, true);
        }

        public SubMap<K,V> descendingMap() {
            return new SubMap<K,V>(m, lo, loInclusive,
                                   hi, hiInclusive, !isDescending);
        }

        /* ----------------  Relational methods -------------- */

        public Map.Entry<K,V> ceilingEntry(K key) {
            return getNearEntry(key, (m.GT|m.EQ));
        }

        public K ceilingKey(K key) {
            return getNearKey(key, (m.GT|m.EQ));
        }

        public Map.Entry<K,V> lowerEntry(K key) {
            return getNearEntry(key, (m.LT));
        }

        public K lowerKey(K key) {
            return getNearKey(key, (m.LT));
        }

        public Map.Entry<K,V> floorEntry(K key) {
            return getNearEntry(key, (m.LT|m.EQ));
        }

        public K floorKey(K key) {
            return getNearKey(key, (m.LT|m.EQ));
        }

        public Map.Entry<K,V> higherEntry(K key) {
            return getNearEntry(key, (m.GT));
        }

        public K higherKey(K key) {
            return getNearKey(key, (m.GT));
        }

        public K firstKey() {
            return isDescending? highestKey() : lowestKey();
        }

        public K lastKey() {
            return isDescending? lowestKey() : highestKey();
        }

        public Map.Entry<K,V> firstEntry() {
            return isDescending? highestEntry() : lowestEntry();
        }

        public Map.Entry<K,V> lastEntry() {
            return isDescending? lowestEntry() : highestEntry();
        }

        public Map.Entry<K,V> pollFirstEntry() {
            return isDescending? removeHighest() : removeLowest();
        }

        public Map.Entry<K,V> pollLastEntry() {
            return isDescending? removeLowest() : removeHighest();
        }

        /* ---------------- Submap Views -------------- */

        public NavigableSet<K> keySet() {
            KeySet<K> ks = keySetView;
            return (ks != null) ? ks : (keySetView = new KeySet(this));
        }

        public NavigableSet<K> navigableKeySet() {
            KeySet<K> ks = keySetView;
            return (ks != null) ? ks : (keySetView = new KeySet(this));
        }

        public Collection<V> values() {
            Collection<V> vs = valuesView;
            return (vs != null) ? vs : (valuesView = new Values(this));
        }

        public Set<Map.Entry<K,V>> entrySet() {
            Set<Map.Entry<K,V>> es = entrySetView;
            return (es != null) ? es : (entrySetView = new EntrySet(this));
        }

        public NavigableSet<K> descendingKeySet() {
            return descendingMap().navigableKeySet();
        }

        Iterator<K> keyIterator() {
            return new SubMapKeyIterator();
        }

        Iterator<V> valueIterator() {
            return new SubMapValueIterator();
        }

        Iterator<Map.Entry<K,V>> entryIterator() {
            return new SubMapEntryIterator();
        }

        /**
         * Variant of main Iter class to traverse through submaps.
         */
        abstract class SubMapIter<T> implements Iterator<T> {
            /** the last node returned by next() */
            SearchResults<K,V> lastReturned;
            /** the next node to return from next(); */
            SearchResults<K,V> next;
            /** Cache of next value field to maintain weak consistency */
            V nextValue;

            SubMapIter() {
                next = isDescending ? hiNode() : loNode();
                if (next == null)
                    return;                    
                Object x = (m.valueProxy == null) ? next.contents.values[next.index] : m.valueProxy;
                if (!inBounds((K) next.contents.keys[next.index]))
                    next = null;
                else
                    nextValue = (V) x;
            }

            public final boolean hasNext() {
                return next != null;
            }

            final void advance() {
                if (next == null)
                    throw new NoSuchElementException();
                lastReturned = next;
                if (isDescending)
                    descend();
                else
                    ascend();
            }

            private void ascend() {
                next = m.immediateSuccessor(next);
                if (next == null)
                    return;
                Object x = (m.valueProxy == null) ? next.contents.values[next.index] : m.valueProxy;
                if (tooHigh((K) next.contents.keys[next.index]))
                    next = null;
                else
                    nextValue = (V) x;
            }

            private void descend() {
                next = m.findNear((K) lastReturned.contents.keys[lastReturned.index], LT);
                if (next == null)
                    return;
                Object x = (m.valueProxy == null) ? next.contents.values[next.index] : m.valueProxy;
                if (tooLow((K) next.contents.keys[next.index]))
                    next = null;
                else
                    nextValue = (V) x;
            }

            public void remove() {
                SearchResults<K,V> l = lastReturned;
                if (l == null)
                    throw new IllegalStateException();
                m.remove((K) l.contents.keys[l.index]);
                lastReturned = null;
            }

        }

        final class SubMapValueIterator extends SubMapIter<V> {
            public V next() {
                V v = nextValue;
                advance();
                return v;
            }
        }

        final class SubMapKeyIterator extends SubMapIter<K> {
            public K next() {
                SearchResults<K,V> n = next;
                advance();
                return (K) n.contents.keys[n.index];
            }
        }

        final class SubMapEntryIterator extends SubMapIter<Map.Entry<K,V>> {
            public Map.Entry<K,V> next() {
                SearchResults<K,V> n = next;
                V v = nextValue;
                advance();
                K k = (K) n.contents.keys[n.index];
                return new AbstractMap.SimpleImmutableEntry<K,V>(k, v);
            }
        }
    }

}