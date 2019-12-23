fn main() {
    let mut a: Vec<u64> = vec![1];
    for n in 1..20 {
        let mut x = 4 * a[n - 1];
        for j in 0..(n - 1) {
            x += a[j] * a[n - 2 - j]
        }
        a.push(x);
    }
    println!("{:?}", a);
}