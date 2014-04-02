void merge(int[] a, int low, int mid, int high)
{
    int[] b = new int[1000];;
    int i = low, j = mid + 1, k = 0;
  
    while (i <= mid && j <= high) {
        if (a[i] <= a[j]) {
            b[k] = a[i];
            k++; i++;
        }
        else {
            b[k] = a[j];
            k++; j++;
        }
    }
    while (i <= mid) {
        b[k] = a[i];
        k++; i++;
    }
  
    while (j <= high) {
        b[k] = a[j];
        k++; j++;
    }
  
    k--;
    while (k >= 0) {
        a[low + k] = b[k];
        k--;
    }
}
  
void mergesort(int[] a, int low, int high)
{
    if (low < high) {
        int m = (high + low)/2;
        mergesort(a, low, m);
        mergesort(a, m + 1, high);
        merge(a, low, m, high);
    }
}

int main() {
  int[] array = new int[1000];
  int i = 0;
  while (i<array.length) {
    array[i] = 1000-i;
    i++;
  }
  mergesort(array, 0, 999);
  for (int x : array) {
    printInt(x);
  }
return 0;
}
