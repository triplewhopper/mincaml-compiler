#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <assert.h>

//#define ACCESS_CHECK

struct object_t {
	int a1, a2, a3, a4;
	float *a5, *a6;
	char a7;
	float *a8, *a9, *a10;
};

struct array_t {
	int length;
	int elem_size;
	char array[0];
};

typedef float vec3[3];
#define Vec3(x) float *x = (float[3]){0, 0, 0}

struct object_t *objects = (struct object_t[60]) {0};

int *size = (int[]) {128, 128};
int *dbg = (int[]) {0};
Vec3(screen);
Vec3(vp);
Vec3(view);
Vec3(light);
float *cos_v = (float[]) {0, 0}, *sin_v = (float[]) {0, 0};
float *beam = (float[]) {255};
float **and_net, ***or_net;

float *temp = (float[14]) {0}, *cs_temp = (float[16]) {0};

void init() {
	{
		and_net = calloc(50, sizeof(int *));
		and_net[0] = calloc(1, sizeof(int));
		and_net[0][0] = -1;
		for (int i = 1; i < 50; i++) {
			and_net[i] = and_net[0];
		}
	}
	or_net = calloc(1, sizeof(int **));
	or_net[0] = calloc(1, sizeof(int *));
	or_net[0][0] = and_net[0];
}

char min_caml_not(char x) {
	return !x;
}

float *solver_dist = (float[1]) {0};

Vec3(vscan);

int *intsec_rectside = (int[1]) {0};

float *tmin = (float[]) {1e9};
Vec3(crashed_point);
int *crashed_object = (int[1]) {0};
int *end_flag = (int[]) {0};
Vec3(viewpoint);
Vec3(nvector);
Vec3(rgb);
Vec3(texture_color);
Vec3(solver_w_vec);
Vec3(chkinside_p);
Vec3(isoutside_q);
Vec3(nvector_w);
float *scan_d = (float[]) {0};
float *scan_offset = (float[]) {0};
float *scan_sscany = (float[]) {0};
float *scan_met1 = (float[]) {0};
Vec3(wscan);

char buffer[3000000];
size_t buffer_pos = 0;

char min_caml_print_byte(int x) {
	assert(buffer_pos < 3000000);
	buffer[buffer_pos++] = x;
	return 0;
}

char min_caml_print_int(int x) {
    if (x == 0) {
        min_caml_print_byte('0');
        return 0;
    }
    if (x < 0) {
        min_caml_print_byte('-');
        x = -x;
    }
    char buf[12];
    int pos = 0;
    while (x > 0) {
        buf[pos++] = x % 10 + '0';
        x /= 10;
    }
    for (int i = pos - 1; i >= 0; i--) {
        min_caml_print_byte(buf[i]);
    }
    return 0;
//	switch (x) {
//		case 768:
//			min_caml_print_byte('7');
//			min_caml_print_byte('6');
//			min_caml_print_byte('8');
//			break;
//		case 255:
//			min_caml_print_byte('2');
//			min_caml_print_byte('5');
//			min_caml_print_byte('5');
//			break;
//		default:
//			assert(0);
//	}
	return 0;
}

int min_caml_read_int(char x) {
	int i;
	assert(scanf("%d", &i) == 1);
	return i;
}

float min_caml_float_of_int(int x) {
	return (float) x;
}

float min_caml_abs_float(float x) {
	return fabs(x);
}


//char min_caml_print_int(int x) {
//	return printf("%d", x);
//}

int min_caml_int_of_float(float x) {
	return (int) trunc(x);
}

//void* array_read(struct array_t array, int index){
//    return array.array + array.elem_size * index;
//}

#ifdef ACCESS_CHECK
struct array_t min_caml_create_array_int_array(int length, int* val){
#else

int **min_caml_create_array_int_array(int length, int *val) {
#endif
	int **array = calloc(length, sizeof(int *));
	for (int i = 0; i < length; i++) {
		array[i] = val;
	}
#ifdef ACCESS_CHECK
	return (struct array_t){length, sizeof(int*), (char*)array};
#else
	return array;
#endif
}

#ifdef ACCESS_CHECK
struct array_t min_caml_create_array_int(int length, int val){
#else

int *min_caml_create_array_int(int length, int val) {
#endif

	int *array = calloc(length, sizeof(int));
	for (int i = 0; i < length; i++) {
		array[i] = val;
	}
#ifdef ACCESS_CHECK
	return (struct int_array_t){length, sizeof(int), array};
#else
	return array;
#endif
}

#ifdef ACCESS_CHECK
struct array_t min_caml_create_array_float(int length, float val){
#else

float *min_caml_create_array_float(int length, float val) {
#endif

	float *array = calloc(length, sizeof(float));
	for (int i = 0; i < length; i++) {
		array[i] = val;
	}
#ifdef ACCESS_CHECK
	return (struct float_array_t){length, sizeof(float), array};
#else
	return array;
#endif
}

float min_caml_read_float(char x) {
	float f;
	assert(scanf("%f", &f) == 1);
	return f;
}
char min_caml_print_newline(char x) {
    min_caml_print_byte('\n');
    return 0;
}

float min_caml_cos(float x) {
	return cosf(x);
}

float min_caml_sin(float x) {
	return sinf(x);
}

float min_caml_sqrt(float x) {
	return sqrtf(x);
}

float min_caml_atan(float x) {
	return atanf(x);
}

float min_caml_floor(float x) {
	return floorf(x);
}

char min_caml_debug_raytracing(int nref, float energy, char crashed_p) {
	fprintf(stderr, "raytracing %d %f %s >>>\n", nref, energy, crashed_p ? "true" : "false");
	return 0;
}

char min_caml_debug_raytracing2(int nref, float energy, char crashed_p) {
	fprintf(stderr, "raytracing %d %f %s <<<\n", nref, energy, crashed_p ? "true" : "false");
	return 0;
}

char min_caml_debug_tracer(float *viewpoint, float *vscan, float t) {
	fprintf(stderr, "tracer (%f, %f, %f) (%f, %f, %f) %f\n", viewpoint[0], viewpoint[1], viewpoint[2], vscan[0],
			vscan[1], vscan[2], t);
	return 0;
}

char min_caml_debug_scan_point(float sscanx) {
	fprintf(stderr, "sscanx = %f\n", sscanx);
	return 0;
}

char min_caml_debug_read_environ_v1_v2(float v1, float v2) {
	fprintf(stderr, "v1 = %f, v2 = %f\n", v1, v2);
	fprintf(stderr, "cos(v1) = %f, sin(v1) = %f\n", cosf(v1), sinf(v1));
	fprintf(stderr, "cos(v2) = %f, sin(v2) = %f\n", cosf(v2), sinf(v2));
	return 0;
}

char min_caml_debug_read_environ_view(char _) {
	fprintf(stderr, "cos_v: %f %f, sin_v: %f %f\n", cos_v[0], cos_v[1], sin_v[0], sin_v[1]);
	fprintf(stderr, "vp: %f %f %f\n", vp[0], vp[1], vp[2]);
	fprintf(stderr, "screen: %f %f %f\n", screen[0], screen[1], screen[2]);
	fprintf(stderr, "view: %f %f %f\n", view[0], view[1], view[2]);
	return 0;
}

extern int caml_main();

int main() {
//    fprintf(stderr, "address of size: %p\n", size);
//    fprintf(stderr, "address of dbg: %p\n", dbg);
//    fprintf(stderr, "address of screen: %p\n", screen);
//    fprintf(stderr, "address of vp: %p\n", vp);
//    fprintf(stderr, "address of view: %p\n", view);
//    fprintf(stderr, "address of light: %p\n", light);
//    fprintf(stderr, "address of cos_v: %p\n", cos_v);
//    fprintf(stderr, "address of sin_v: %p\n", sin_v);
	init();
	caml_main();
	fwrite(buffer, 1, buffer_pos, stdout);
	return 0;
}
