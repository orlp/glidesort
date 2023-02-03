// Nearly-Optimal Mergesorts: Fast, Practical Sorting Methods That Optimally
// Adapt to Existing Runs by J. Ian Munro and Sebastian Wild.
//
// This method forms a binary merge tree, where each internal node corresponds
// to a splitting point between the adjacent runs that have to be merged. If we
// visualize our array as the number line from 0 to 1, we want to find the
// dyadic fraction with smallest denominator that lies between the midpoints of
// our to-be-merged slices. The exponent in the dyadic fraction indicates the
// desired depth in the binary merge tree this internal node wishes to have.
// This does not always correspond to the actual depth due to the inherent
// imbalance in runs, but we follow it as closely as possible.
//
// As an optimization we rescale the number line from [0, 1) to [0, 2^62). Then
// finding the simplest dyadic fraction between midpoints corresponds to finding
// the most significant bit difference of the midpoints. We save scale_factor =
// ceil(2^62 / n) to perform this rescaling using a multiplication, avoiding
// having to repeatedly do integer divides. This rescaling isn't exact when n is
// not a power of two since we use integers and not reals, but the result is
// very close, and in fact when n < 2^30 the resulting tree is equivalent as the
// approximation errors stay entirely in the lower order bits.
//
// Thus for the splitting point between two adjacent slices [a, b) and [b, c)
// the desired depth of the corresponding merge node is CLZ((a+b)*f ^ (b+c)*f),
// where CLZ counts the number of leading zeros in an integer and f is our scale
// factor. Note that we omitted the division by two in the midpoint
// calculations, as this simply shifts the bits by one position (and thus always
// adds one to the result), and we only care about the relative depths.
//
// It is important that for any three slices [a, b), [b, c), [c, d) with
// a < b < c < d we have that tree_depth([a, b), [b, c)) != tree_depth([b, c),
// [c, d)), as this would break our implicit tree structure and potentially our
// log2(n) stack size limit. This is proven in the original paper, but our
// approximation complicates things. Let x, y, z respectively be (a+b)*f,
// (b+c)*f, (c+d)*f, then what we wish to prove is CLZ(x ^ y) != CLZ(y ^ z).
//
// Because a < c we have x < y, and similarly we have y < z. Since x < y we can
// conclude that CLZ(x ^ y) will be determined by a bit position where x is 0
// and y is 1, as it is the most significant bit difference. Apply a similar
// logic for y and z and you would conclude that it is determined by a bit
// position where y is 0 and z is 1. Thus looking at y it can't be the same bit
// position in both cases, and we must have CLZ(x ^ y) != CLZ(y ^ z).
//
// Finally, if we try to upper bound z giving z = ceil(2^62 / n) * (n-1 + n) then
//    z < (2^62 / n + 1) * 2n
//    z < 2^63 + 2n
// So as long as n < 2^62 we find that z < 2^64, meaning our operations do not
// overflow.
pub fn merge_tree_scale_factor(n: usize) -> u64 {
    ((1 << 62) + n as u64 - 1) / n as u64
}

pub fn merge_tree_depth(left: usize, mid: usize, right: usize, scale_factor: u64) -> u8 {
    let x = left as u64 + mid as u64;
    let y = mid as u64 + right as u64;
    ((scale_factor * x) ^ (scale_factor * y)).leading_zeros() as u8
}
