#define _POSIX_C_SOURCE 200809L

#include <gtk/gtk.h>
#include <gdk/gdkkeysyms.h>
#include <math.h>
#include <ctype.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>

#define MAX_STACK       256
#define MAX_BUFF        1024
#define EPSILON         1e-9
#define CHUNK_SIZE      32
#define CHECK_PTR(p) if(!(p)) { fprintf(stderr, "[FATAL] Falha de alocacao em %d\n", __LINE__); exit(1); }

typedef enum {
    OP_PUSH, OP_ADD, OP_SUB, OP_MUL, 
    OP_DIV, OP_MOD, OP_POW, OP_HALT
} OpCode;
typedef struct {
    OpCode code;
    double arg; 
} Instrucao;
typedef struct {
    Instrucao *text_segment;
    size_t size, capacity;
} Bytecode;
typedef struct {
    double data[MAX_STACK];
    double *sp;  /* Stack Pointer */
    int err_flag;
} VM;

typedef struct node {
    char *expr_str;
    char *res_str;
    struct node *next;
} NodeHist;
typedef struct {
    GtkWidget *win;
    GtkWidget *lbl_e, *lbl_r;
    GtkWidget *box_hist, *list_hist;
    char buf_in[512], buf_out[MAX_BUFF];
    NodeHist *head;
    int state_done;
} Ctx;

static void vm_reset(VM *vm) {
    vm->sp = vm->data;
    vm->err_flag = 0;
}

static void push(VM *vm, double v) {
    if((vm->sp - vm->data) >= MAX_STACK) {
        fprintf(stderr, "[VM] Stack Overflow\n");
        vm->err_flag = 1; return;
    }
    *vm->sp++ = v;
}

static double pop(VM *vm) {
    if(vm->sp == vm->data) {
        fprintf(stderr, "[VM] Stack Underflow\n");
        vm->err_flag = 1; return 0.0;
    }
    return *--vm->sp;
}

static double vm_cpu_run(VM *vm, Bytecode *prog) {
    Instrucao *ip = prog->text_segment; /* Instruction Pointer */
    double a, b;
    
    vm_reset(vm);
    for (;;) {
        switch (ip->code) {
            case OP_HALT: return pop(vm);
            case OP_PUSH: push(vm, ip->arg); break;
            /* Aritmetica Inversa (Stack) */
            case OP_ADD: b=pop(vm); a=pop(vm); push(vm, a+b); break;
            case OP_SUB: b=pop(vm); a=pop(vm); push(vm, a-b); break;
            case OP_MUL: b=pop(vm); a=pop(vm); push(vm, a*b); break;
            case OP_DIV: b=pop(vm); a=pop(vm);
                if(fabs(b) < EPSILON) { vm->err_flag=1; return 0; }
                push(vm, a/b); break;
            case OP_MOD: b=pop(vm); a=pop(vm);
                if(fabs(b) < EPSILON) { vm->err_flag=1; return 0; }
                push(vm, fmod(a,b)); break;
            case OP_POW: b=pop(vm); a=pop(vm); push(vm, pow(a,b)); break;
        }
        if(vm->err_flag) return 0.0;
        ip++;
    }
}

static void bc_init(Bytecode *b) {
    b->text_segment = malloc(CHUNK_SIZE * sizeof(Instrucao));
    CHECK_PTR(b->text_segment);
    b->size = 0;
    b->capacity = CHUNK_SIZE;
}

static void bc_emit(Bytecode *b, OpCode op, double v) {
    if (b->size >= b->capacity) {
        b->capacity <<= 1;
        b->text_segment = realloc(b->text_segment, b->capacity * sizeof(Instrucao));
        CHECK_PTR(b->text_segment);
    }
    b->text_segment[b->size].code = op;
    b->text_segment[b->size].arg = v;
    b->size++;
}

static void bc_free(Bytecode *b) {
    if(b->text_segment) free(b->text_segment);
    b->text_segment = NULL;
    b->size = 0;
}

static int precedence(char op) {
    if(op=='^') return 3;
    if(op=='*'||op=='/'||op=='%') return 2;
    if(op=='+'||op=='-') return 1;
    return 0;
}

static OpCode token_to_op(char c) {
    switch(c) {
        case '+': return OP_ADD; case '-': return OP_SUB;
        case '*': return OP_MUL; case '/': return OP_DIV;
        case '%': return OP_MOD; case '^': return OP_POW;
        default: return OP_HALT;
    }
}

static int jit_compile(const char *src, Bytecode *b) {
    char op_stack[MAX_STACK], *top = op_stack, num_buf[64];
    const char *p = src;
    int k;

    fprintf(stderr, "[JIT] Compilando: %s\n", src);

    bc_init(b);
    while (*p) {
        if (isspace(*p)) { p++; continue; }
        
        /* Lexer simples para numeros */
        if (isdigit(*p) || *p=='.') {
            k = 0;
            while(isdigit(*p) || *p=='.') if(k<63) num_buf[k++] = *p++;
            num_buf[k] = 0;
            bc_emit(b, OP_PUSH, strtod(num_buf, NULL));
            continue;
        }
        
        if (strchr("+-*/%^()", *p)) {
            if (*p == '(') *top++ = *p;
            else if (*p == ')') {
                while (top > op_stack && *(top-1) != '(')
                    bc_emit(b, token_to_op(*--top), 0);
                if (top == op_stack) return 0;
                top--;
            } else {
                while (top > op_stack && *(top-1) != '(' && 
                       precedence(*(top-1)) >= precedence(*p)) {
                    if (*p=='^' && *(top-1)=='^') break;
                    bc_emit(b, token_to_op(*--top), 0);
                }
                *top++ = *p;
            }
        }
        p++;
    }
    
    while (top > op_stack) {
        if (*(top-1) == '(') return 0;
        bc_emit(b, token_to_op(*--top), 0);
    }
    bc_emit(b, OP_HALT, 0);
    return 1;
}

static void hist_append(Ctx *ctx, const char *e, const char *r) {
    NodeHist *n = malloc(sizeof(NodeHist));
    GtkWidget *row, *vbox, *l1, *l2;
    char buf[MAX_BUFF];

    CHECK_PTR(n);
    n->expr_str = strdup(e);
    n->res_str = strdup(r);
    n->next = ctx->head;
    ctx->head = n;
    row = gtk_list_box_row_new();
    vbox = gtk_box_new(GTK_ORIENTATION_VERTICAL, 2);
    snprintf(buf, MAX_BUFF, "%s =", e);
    l1 = gtk_label_new(buf);
    gtk_widget_set_halign(l1, GTK_ALIGN_START);
    gtk_style_context_add_class(gtk_widget_get_style_context(l1), "h-eq");

    l2 = gtk_label_new(r);
    gtk_widget_set_halign(l2, GTK_ALIGN_END);
    gtk_style_context_add_class(gtk_widget_get_style_context(l2), "h-res");

    gtk_box_pack_start(GTK_BOX(vbox), l1, FALSE, FALSE, 0);
    gtk_box_pack_start(GTK_BOX(vbox), l2, FALSE, FALSE, 0);
    gtk_container_add(GTK_CONTAINER(row), vbox);
    g_object_set_data_full(G_OBJECT(row), "raw_val", strdup(r), free);
    
    gtk_list_box_prepend(GTK_LIST_BOX(ctx->list_hist), row);
    gtk_widget_show_all(row);
}

static void hist_clear(Ctx *ctx) {
    NodeHist *aux;
    GList *children, *iter;
    
    while (ctx->head) {
        aux = ctx->head;
        ctx->head = aux->next;
        free(aux->expr_str); free(aux->res_str); free(aux);
    }
    
    children = gtk_container_get_children(GTK_CONTAINER(ctx->list_hist));
    for(iter=children; iter; iter=iter->next) 
        gtk_widget_destroy(GTK_WIDGET(iter->data));
    g_list_free(children);
}

static void ui_update(Ctx *ctx) {
    gtk_label_set_text(GTK_LABEL(ctx->lbl_e), ctx->buf_out);
    gtk_label_set_text(GTK_LABEL(ctx->lbl_r), ctx->buf_in);
}

static void calc_step(Ctx *ctx, const char *key) {
    Bytecode prog;
    VM vm;
    double res;
    char res_fmt[64], full_expr[MAX_BUFF];

    if (!strcmp(key, "C")) {
        ctx->buf_in[0]='0'; ctx->buf_in[1]=0; 
        ctx->buf_out[0]=0;
        ctx->state_done = 0;
        ui_update(ctx);
        return;
    }

    if (!strcmp(key, "=")) {
        if(ctx->state_done) return;
        
        snprintf(full_expr, MAX_BUFF, "%s%s", ctx->buf_out, ctx->buf_in);
        
        if (jit_compile(full_expr, &prog)) {
            res = vm_cpu_run(&vm, &prog);
            bc_free(&prog);
            
            if (!vm.err_flag) {
                snprintf(res_fmt, 64, "%.10g", res);
                hist_append(ctx, full_expr, res_fmt);
                snprintf(ctx->buf_out, MAX_BUFF, "%s =", full_expr);
                strncpy(ctx->buf_in, res_fmt, 512);
                ctx->state_done = 1;
            } else {
                strcpy(ctx->buf_in, "Erro Execucao");
                ctx->state_done = 1;
            }
        } else {
            strcpy(ctx->buf_in, "Erro Sintaxe");
            bc_free(&prog);
            ctx->state_done = 1;
        }
        ui_update(ctx);
        return;
    }

    if (strchr("+-*/%^", key[0]) && !key[1]) {
        if (ctx->state_done) {
            if (!isdigit(ctx->buf_in[0]) && ctx->buf_in[0]!='-') strcpy(ctx->buf_in, "0");
            ctx->buf_out[0]=0; ctx->state_done=0;
        }
        strncat(ctx->buf_out, ctx->buf_in, MAX_BUFF-strlen(ctx->buf_out)-1);
        strncat(ctx->buf_out, " ", MAX_BUFF-strlen(ctx->buf_out)-1);
        strncat(ctx->buf_out, key, MAX_BUFF-strlen(ctx->buf_out)-1);
        strncat(ctx->buf_out, " ", MAX_BUFF-strlen(ctx->buf_out)-1);
        strcpy(ctx->buf_in, "0");
        ui_update(ctx);
        return;
    }

    if (ctx->state_done) {
        strcpy(ctx->buf_in, "0"); ctx->buf_out[0]=0; ctx->state_done=0;
    }
    if (!strcmp(ctx->buf_in, "0") && strcmp(key, ".")) strncpy(ctx->buf_in, key, 512);
    else strncat(ctx->buf_in, key, 512-strlen(ctx->buf_in)-1);
    ui_update(ctx);
}

static void cb_click(GtkWidget *w, gpointer data) {
    const char *id = g_object_get_data(G_OBJECT(w), "id");
    if(id) calc_step((Ctx*)data, id);
}

static void cb_hist_sel(GtkListBox *b, GtkListBoxRow *row, gpointer data) {
    Ctx *c = (Ctx*)data;
    const char *raw = g_object_get_data(G_OBJECT(row), "raw_val");
    (void)b;
    if (raw) {
        strncpy(c->buf_in, raw, 512); 
        c->buf_out[0]=0; 
        c->state_done=1;
        ui_update(c);
    }
}

static void cb_toggle(GtkWidget *w, gpointer data) {
    Ctx *c = (Ctx*)data;
    int vis = gtk_widget_get_visible(c->box_hist);
    (void)w;
    gtk_widget_set_visible(c->box_hist, !vis);
    gtk_window_resize(GTK_WINDOW(c->win), vis ? 320 : 560, 480);
}

static void cb_clear_h(GtkWidget *w, gpointer data) { (void)w; hist_clear((Ctx*)data); }

static gboolean cb_keypress(GtkWidget *w, GdkEventKey *ev, gpointer data) {
    char buf[2]={0}; const char *k=NULL;
    (void)w;
    if (ev->keyval >= GDK_KEY_0 && ev->keyval <= GDK_KEY_9) {
        buf[0] = ev->keyval - GDK_KEY_0 + '0'; k=buf;
    } else if (ev->keyval >= GDK_KEY_KP_0 && ev->keyval <= GDK_KEY_KP_9) {
        buf[0] = ev->keyval - GDK_KEY_KP_0 + '0'; k=buf;
    } else {
        switch(ev->keyval) {
            case GDK_KEY_Return: case GDK_KEY_KP_Enter: k="="; break;
            case GDK_KEY_BackSpace: k="C"; break;
            case GDK_KEY_plus: case GDK_KEY_KP_Add: k="+"; break;
            case GDK_KEY_minus: case GDK_KEY_KP_Subtract: k="-"; break;
            case GDK_KEY_asterisk: case GDK_KEY_KP_Multiply: k="*"; break;
            case GDK_KEY_slash: case GDK_KEY_KP_Divide: k="/"; break;
            case GDK_KEY_period: case GDK_KEY_KP_Decimal: k="."; break;
            case GDK_KEY_asciicircum: k="^"; break;
            case GDK_KEY_percent: k="%"; break;
        }
    }
    if(k) { calc_step((Ctx*)data, k); return TRUE; }
    return FALSE;
}

static void init_styles(void) {
    GtkCssProvider *p = gtk_css_provider_new();
    const char *css = 
        "window { background: #222; }"
        "label { font-family: monospace; color: #ccc; }"
        ".d-res { font-size: 36px; font-weight: bold; color: #fff; }"
        ".d-eq { font-size: 14px; color: #888; }"
        "button { background: #333; color: #eee; border: 1px solid #111; border-radius: 0; }"
        "button:hover { background: #444; }"
        ".op { background: #222; color: #fa0; }"
        ".eq { background: #fa0; color: #000; font-weight: bold; }"
        ".eq:hover { background: #ffcc00; }"
        ".h-box { background: #252525; border-left: 1px solid #444; }"
        ".h-eq { font-size: 10px; color: #666; }"
        ".h-res { font-size: 14px; font-weight: bold; color: #bbb; }";
    
    gtk_css_provider_load_from_data(p, css, -1, NULL);
    gtk_style_context_add_provider_for_screen(gdk_display_get_default_screen(gdk_display_get_default()),
        GTK_STYLE_PROVIDER(p), GTK_STYLE_PROVIDER_PRIORITY_APPLICATION);
    g_object_unref(p);
}

int main(int argc, char **argv) {
    Ctx *ctx;
    GtkWidget *root, *main_box, *top_bar, *btn_h, *btn_clr, *disp_box, *keypad, *scroller;
    int i;
    struct { char *lbl, *id, *cls; int x,y,w,h; } keys[] = {
        {"CLR","C","",0,0,1,1}, {"^","^","op",1,0,1,1}, {"%","%","op",2,0,1,1}, {"/","/","op",3,0,1,1},
        {"7","7","",0,1,1,1}, {"8","8","",1,1,1,1}, {"9","9","",2,1,1,1}, {"*","*","op",3,1,1,1},
        {"4","4","",0,2,1,1}, {"5","5","",1,2,1,1}, {"6","6","",2,2,1,1}, {"-","-","op",3,2,1,1},
        {"1","1","",0,3,1,1}, {"2","2","",1,3,1,1}, {"3","3","",2,3,1,1}, {"+","+","op",3,3,1,1},
        {"0","0","",0,4,2,1}, {".",".","",2,4,1,1}, {"=","=","eq",3,4,1,1}
    };

    gtk_init(&argc, &argv);
    
    ctx = calloc(1, sizeof(Ctx));
    CHECK_PTR(ctx);
    strcpy(ctx->buf_in, "0");

    ctx->win = gtk_window_new(GTK_WINDOW_TOPLEVEL);
    gtk_window_set_title(GTK_WINDOW(ctx->win), "Calc JIT/VM (LP2)");
    gtk_window_set_default_size(GTK_WINDOW(ctx->win), 320, 480);
    g_signal_connect(ctx->win, "destroy", G_CALLBACK(gtk_main_quit), NULL);
    g_signal_connect(ctx->win, "key-press-event", G_CALLBACK(cb_keypress), ctx);

    root = gtk_box_new(GTK_ORIENTATION_HORIZONTAL, 0);
    gtk_container_add(GTK_CONTAINER(ctx->win), root);
    main_box = gtk_box_new(GTK_ORIENTATION_VERTICAL, 5);
    gtk_container_set_border_width(GTK_CONTAINER(main_box), 10);
    gtk_box_pack_start(GTK_BOX(root), main_box, TRUE, TRUE, 0);
    top_bar = gtk_box_new(GTK_ORIENTATION_HORIZONTAL, 0);
    btn_h = gtk_button_new_with_label("Hist");
    g_signal_connect(btn_h, "clicked", G_CALLBACK(cb_toggle), ctx);
    gtk_box_pack_start(GTK_BOX(top_bar), btn_h, FALSE, FALSE, 0);
    gtk_box_pack_start(GTK_BOX(main_box), top_bar, FALSE, FALSE, 5);
    disp_box = gtk_box_new(GTK_ORIENTATION_VERTICAL, 0);
    ctx->lbl_e = gtk_label_new("");
    gtk_widget_set_halign(ctx->lbl_e, GTK_ALIGN_END);
    gtk_style_context_add_class(gtk_widget_get_style_context(ctx->lbl_e), "d-eq");
    
    ctx->lbl_r = gtk_label_new("0");
    gtk_widget_set_halign(ctx->lbl_r, GTK_ALIGN_END);
    gtk_style_context_add_class(gtk_widget_get_style_context(ctx->lbl_r), "d-res");
    
    gtk_box_pack_start(GTK_BOX(disp_box), ctx->lbl_e, FALSE, FALSE, 0);
    gtk_box_pack_start(GTK_BOX(disp_box), ctx->lbl_r, FALSE, FALSE, 0);
    gtk_box_pack_start(GTK_BOX(main_box), disp_box, FALSE, FALSE, 15);
    keypad = gtk_grid_new();
    gtk_grid_set_row_spacing(GTK_GRID(keypad), 4);
    gtk_grid_set_column_spacing(GTK_GRID(keypad), 4);
    gtk_grid_set_row_homogeneous(GTK_GRID(keypad), TRUE);
    gtk_grid_set_column_homogeneous(GTK_GRID(keypad), TRUE);
    gtk_box_pack_start(GTK_BOX(main_box), keypad, TRUE, TRUE, 0);

    for (i=0; i<(int)(sizeof(keys)/sizeof(keys[0])); i++) {
        GtkWidget *b = gtk_button_new_with_label(keys[i].lbl);
        if (*keys[i].cls) 
            gtk_style_context_add_class(gtk_widget_get_style_context(b), keys[i].cls);
        
        g_object_set_data(G_OBJECT(b), "id", keys[i].id);
        g_signal_connect(b, "clicked", G_CALLBACK(cb_click), ctx);
        gtk_widget_set_hexpand(b, TRUE); 
        gtk_widget_set_vexpand(b, TRUE);
        gtk_grid_attach(GTK_GRID(keypad), b, keys[i].x, keys[i].y, keys[i].w, keys[i].h);
    }
    ctx->box_hist = gtk_box_new(GTK_ORIENTATION_VERTICAL, 5);
    gtk_style_context_add_class(gtk_widget_get_style_context(ctx->box_hist), "h-box");
    gtk_widget_set_size_request(ctx->box_hist, 200, -1);

    btn_clr = gtk_button_new_with_label("Limpar Historico");
    g_signal_connect(btn_clr, "clicked", G_CALLBACK(cb_clear_h), ctx);
    gtk_box_pack_start(GTK_BOX(ctx->box_hist), btn_clr, FALSE, FALSE, 5);
    
    scroller = gtk_scrolled_window_new(NULL,NULL);
    ctx->list_hist = gtk_list_box_new();
    g_signal_connect(ctx->list_hist, "row-activated", G_CALLBACK(cb_hist_sel), ctx);
    gtk_container_add(GTK_CONTAINER(scroller), ctx->list_hist);
    gtk_box_pack_start(GTK_BOX(ctx->box_hist), scroller, TRUE, TRUE, 0);
    gtk_box_pack_start(GTK_BOX(root), ctx->box_hist, FALSE, TRUE, 0);
    gtk_widget_show_all(ctx->box_hist);
    gtk_widget_set_visible(ctx->box_hist, FALSE);
    gtk_widget_set_no_show_all(ctx->box_hist, TRUE);

    init_styles();
    gtk_widget_show_all(ctx->win);
    gtk_main();
    return 0;
}
