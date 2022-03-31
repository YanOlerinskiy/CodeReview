#include <iostream>
#include <iomanip>
#include <ostream>
#include <istream>
#include <set>
#include <unordered_set>
#include <map>
#include <unordered_map>
#include <bitset>
#include <vector>
#include <string>
#include <stack>
#include <queue>
#include <deque>
#include <array>
#include <algorithm>
#include <functional>
#include <cmath>
#include <time.h>
#include <random>
#include <chrono>
#include <cassert> 
#include <cstring>
#include <limits>
#include <cstddef>
#include <iterator>

using namespace std;

template<class T>
class Set {
private:
    struct node {
        T val;
        int height;
        size_t sz;
        node* par = nullptr;
        node* left = nullptr;
        node* right = nullptr;
        node() {
            val = T();
            height = -1, sz = 0;
            par = left = right = nullptr;
        }
        node(T val_, int height_) : val(val_), height(height_), sz(1) {
            par = left = right = nullptr;
        }
        node(T val_, int height_, node* par_) : val(val_), height(height_), par(par_), sz(1) {
            left = right = nullptr;
        }
    };

    void destroy(node* a) {
        if (a == nullptr) return;
        destroy(a->left);
        destroy(a->right);
        delete a;
        a = nullptr;
    }
    
    int height(node* a) const {
        if (a == nullptr) return -1;
        return a->height;
    }

    size_t sz(node* a) const {
        if (a == nullptr) return 0;
        return a->sz;
    }

    void setpar(node* a, node* par) {
        if (a == nullptr) return;
        a->par = par;
    }

    void recalc(node* a) {
        if (a == nullptr) return;
        a->height = max(height(a->left), height(a->right)) + 1;
        a->sz = 1 + sz(a->left) + sz(a->right);
        setpar(a->left, a);
        setpar(a->right, a);
    }

    int diff(node* a) const {
        if (a == nullptr) return 0;
        return height(a->left) - height(a->right);
    }

    bool balanced(node* a) const {
        if (a == nullptr) return 1;
        return abs(diff(a)) < 2;
    }

    void leftRotate(node* a) {
        node* b = a->right;
        node* par = a->par;
        a->right = b->left;
        b->left = a;
        if (par != nullptr) {
            if (par->left == a) {
                par->left = b;
            } else {
                par->right = b;
            }
        }
        recalc(a);
        recalc(b);
    }

    void rightRotate(node* a) {
        node* b = a->left;
        node* par = a->par;
        a->left = b->right;
        b->right = a;
        if (par != nullptr) {
            if (par->left == a) {
                par->left = b;
            } else {
                par->right = b;
            }
        }
        recalc(a);
        recalc(b);
    }

    void bigLeftRotate(node* a) {
        rightRotate(a->right);
        leftRotate(a);
    }

    void bigRightRotate(node* a) {
        leftRotate(a->left);
        rightRotate(a);
    }

    node* balance(node* a) {
        if (balanced(a)) return a;
        node* par = a->par;
        bool root = (par == nullptr);
        if (diff(a) == -2) { 
            node* b = a->right;
            if (diff(b) <= 0) {
                leftRotate(a);
                b->par = par;
                if (root) root_ = b;
                return b;
            } else {
                node* c = b->left;
                bigLeftRotate(a);
                c->par = par;
                if (root) root_ = c;
                return c;
            }
        } else if (diff(a) == 2) {
            node* b = a->left;
            if (diff(b) >= 0) {
                rightRotate(a);
                b->par = par;
                if (root) root_ = b;
                return b;
            } else {
                node* c = b->right;
                bigRightRotate(a);
                c->par = par;
                if (root) root_ = c;
                return c;
            }
        } else {
            assert(false);
        }
    }

    node* descendLeft(node* a) const {
        if (a == nullptr) return a;
        while (a->left != nullptr) {
            a = a->left;
        }
        return a;
    }

    node* descendRight(node* a) const {
        if (a == nullptr) return a;
        while (a->right != nullptr) {
            a = a->right;
        }
        return a;
    }

    void erase(node* cur) {
        if (cur->sz == 1) {
            node* par = cur->par;
            if (cur == par->left) {
                par->left = nullptr;
            } else {
                par->right = nullptr;
            }
            delete cur;
            cur = par;
            while (cur != nullptr) {
                recalc(cur);
                cur = balance(cur);
                cur = cur->par;
            }
            return;
        } else {
            if (cur->left != nullptr) {
                node* nw = descendRight(cur->left);
                swap(nw->val, cur->val);
                erase(nw);
            } else {
                node* nw = descendLeft(cur->right);
                swap(nw->val, cur->val);
                erase(nw);
            }
        }
    }

    bool eq(const T& a, const T& b) const {
        return (!(a < b) && !(b < a));
    }

public:
    Set() {
        destroy(root_);
        root_ = nullptr;
    }

    template<typename Iterator>
    Set(Iterator first, Iterator last) {
        destroy(root_);
        root_ = nullptr;
        while (first != last) {
            insert(*first);
            ++first;
        }
    }

    Set(std::initializer_list<T> elems) {
        destroy(root_);
        root_ = nullptr;
        for (auto k : elems) {
            insert(k);
        }
    }

    Set(const Set<T>& other) {
        destroy(root_);
        root_ = nullptr;
        for (auto& k : other) {
            insert(k);
        }
    }

    Set<T> operator= (const Set<T>& other) {
        if (root_ == other.root_) {
            return *this;
        }
        destroy(root_);
        root_ = nullptr;
        for (auto& k : other) {
            insert(k);
        }
        return *this;
    }

    ~Set() {
        destroy(root_);
    }

    size_t size() const {
        return (root_ == nullptr ? 0 : root_->sz);
    }

    bool empty() const {
        return (root_ == nullptr);
    }

    void insert(const T& elem) {
        if (root_ == nullptr) {
            root_ = new node(elem, 0);
            return;
        }
        node* cur = root_;
        while (1) {
            if (eq(cur->val, elem)) {
                return;
            }
            if (elem < cur->val) {
                if (cur->left != nullptr) {
                    cur = cur->left;
                } else {
                    break;
                }
            } else { // cur->val < elem
                if (cur->right != nullptr) {
                    cur = cur->right;
                } else {
                    break;
                }
            }
        }
        node* nw = new node(elem, 0);
        if (elem < cur->val) {
            cur->left = nw;
        } else {
            cur->right = nw;
        }
        while (cur != nullptr) {
            recalc(cur);
            cur = balance(cur);
            cur = cur->par;
        }
    }

    void erase(const T& elem) {
        if (root_ == nullptr) return;
        if (root_->sz == 1) {
            if (eq(root_->val, elem)) {
                delete root_;
                root_ = nullptr;
            }
            return;
        }
        node* cur = root_;
        while (1) {
            if (cur == nullptr) return;
            if (eq(cur->val, elem)) break;
            if (elem < cur->val) {
                cur = cur->left;
            } else {
                cur = cur->right;
            }
        }
        erase(cur);
    }

    struct iterator {
        using iterator_category = bidirectional_iterator_tag;
        using difference_type   = ptrdiff_t;
        using value_type        = node;

        iterator(): ptr(nullptr), end(1) {}
        iterator(node* ptr_): ptr(ptr_), end(0) {
            if (ptr == nullptr) {
                end = 1;
            }
        }
        iterator(node* ptr_, bool end_): ptr(ptr_), end(end_) {
            if (ptr == nullptr) {
                end = 1;
            }
        }

        T& operator*() const {
            assert(end != 1);
            return ptr->val;
        }

        T* operator->() const {
            assert(end != 1);
            return &(ptr->val);
        }

       node* descendLeft(node* a) const {
            if (a == nullptr) return a;
            while (a->left != nullptr) {
                a = a->left;
            }
            return a;
        }

        node* descendRight(node* a) const {
            if (a == nullptr) return a;
            while (a->right != nullptr) {
                a = a->right;
            }
            return a;
        }

        node* findNext(node* a) const {
            if (a->right != nullptr) {
                return descendLeft(a->right);
            }
            while (a->par != nullptr && a->par->val < a->val) {
                a = a->par;
            }
            if (a->par == nullptr) return nullptr;
            return a->par;
        }

        node* findPrev(node* a) const {
            if (a->left != nullptr) {
                return descendRight(a->left);
            }
            while (a->par != nullptr && a->val < a->par->val) {
                a = a->par;
            }
            if (a->par == nullptr) return nullptr;
            return a->par;
        }

        iterator& operator++() {
            assert(end == 0);
            node* nw = findNext(ptr);
            if (nw == nullptr) {
                end = 1;
            } else {
                ptr = nw;
            }
            return *this;
        }

        iterator operator++(int) {
            iterator t = *this;
            ++(*this);
            return t;
        }

        iterator& operator--() {
            if (end) {
                end = 0;
            } else {
                node* nw = findPrev(ptr);
                if (nw != nullptr) {
                    ptr = nw;
                }
            }
            return *this;
        }

        iterator operator--(int) {
            iterator t = *this;
            --(*this);
            return t;
        }

        void print() {
            cout << (ptr == nullptr ? -1 : ptr->val) << " " << end << endl;
        }

        friend bool operator== (const iterator& a, const iterator& other) {
            return a.ptr == other.ptr && a.end == other.end;
        }
        friend bool operator!= (const iterator& a, const iterator& other) {
            return a.ptr != other.ptr || a.end != other.end;
        }

        private: 
        node* ptr = nullptr;
        bool end = 1;
    };

    iterator begin() const {
        return iterator(descendLeft(root_), (empty() ? 1 : 0));
    }

    iterator end() const {
        return iterator(descendRight(root_), 1);
    }

    iterator find(const T& elem) const {
        node* cur = root_;
        while (cur != nullptr) {
            if (eq(elem, cur->val)) return iterator(cur);
            if (elem < cur->val) {
                cur = cur->left;
            } else {
                cur = cur->right;
            }
        }
        return end();
    }

    iterator lower_bound(const T& elem) const {
        node* cur = root_;
        node* best = nullptr;
        while (cur != nullptr) {
            if (eq(elem, cur->val)) return iterator(cur);
            if (elem < cur->val) {
                best = cur;
                cur = cur->left;
            } else {
                cur = cur->right;
            }
        }
        if (best == nullptr) {
            return end();
        } else {
            return iterator(best, 0);
        }
    }
private:
    node* root_ = nullptr;
};