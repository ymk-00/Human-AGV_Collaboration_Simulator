import pygame
import sys
import random
import math
import heapq
import time
import logging
import pandas as pd
import os
import re
import tkinter as tk
from tkinter import filedialog

FAST_MODE = False  # 고속 모드 여부 (기본 False)

logging.basicConfig(
   level=logging.INFO,
   format='%(asctime)s - %(levelname)s - %(message)s',
   handlers=[logging.StreamHandler()]
)

# 색 정의
WHITE   = (245, 245, 230)
BLACK   = (0, 0, 0)
RED     = (200, 0, 0)
GREEN   = (0, 110, 90)
BLUE    = (0, 50, 130)
PURPLE  = (128, 0, 128)
MANGO = (255, 204, 102)
MAX_CAPACITY=10
PATH_COLOR = (200, 150, 255)   # 경로 표시 색상
ITEM_COLOR = (255, 255, 0)    # 아이템 색상
AGV_COUNT_COLOR = (200, 150, 255)
HUMAN_PATH_COLOR  = (100, 200, 255)
HUMAN_COUNT_COLOR = ( 50, 150, 255)

# 우측 상태창 폭   
STATS_WIDTH = 300     
SCREEN_HEIGHT = 800
GRID_SIZE = 20

# 선반 설정
SHELF_UNIT_WIDTH  = 2
SHELF_UNIT_HEIGHT = 7
SHELF_ROWS = 4
SHELF_COLS = 15

# 물류창고 레이아웃 그리드 크기 (40행 × 68열)
WAREHOUSE_ROWS = 40
WAREHOUSE_COLS = 68


shelf_block_width  = SHELF_UNIT_WIDTH * GRID_SIZE
shelf_block_height = SHELF_UNIT_HEIGHT * GRID_SIZE

gap_x = 2 * GRID_SIZE
gap_y = 2 * GRID_SIZE

total_width_with_gap  = SHELF_COLS * shelf_block_width + (SHELF_COLS - 1) * gap_x
total_height_with_gap = SHELF_ROWS * shelf_block_height + (SHELF_ROWS - 1) * gap_y

SIM_WIDTH = total_width_with_gap + 10 * GRID_SIZE
SCREEN_WIDTH = SIM_WIDTH + STATS_WIDTH

margin_x = 5 * GRID_SIZE
margin_y = ((SCREEN_HEIGHT - total_height_with_gap) // 2) // GRID_SIZE * GRID_SIZE

reserved_positions = set()
dropoff_positions = []

pygame.init()
screen = pygame.display.set_mode((SCREEN_WIDTH, SCREEN_HEIGHT))
pygame.display.set_caption("스마트 물류센터 시뮬레이션")
clock = pygame.time.Clock()

# ── 로딩 스플래시 화면 ───────────────────────────────────────
def show_splash(screen, clock, message="데이터 로딩 중… 잠시만 기다려 주세요"):
    screen.fill(WHITE)
    # candidates 변수가 아직 없으므로, 기본 폰트나 직접 지정한 한글 폰트를 사용
    # 기본: None → 시스템 기본 폰트 (영문만)
    # 한글 지원: 'malgun gothic' 등을 명시
    font = pygame.font.SysFont('malgun gothic', 24)
    txt = font.render(message, True, BLACK)
    screen.blit(txt, txt.get_rect(center=screen.get_rect().center))
    pygame.display.flip()
    clock.tick(5)

show_splash(screen, clock)
# ───────────────────────────────────────────────────────────────

time_points = []
completed_orders_points = []
completed_items_points = []
heatmap_data = None
simulation_speed = 1.0

# 폰트 설정 (초기 입력은 크게, 시뮬레이션은 작게, 최종 통계는 크게)
try:
   import platform
   if platform.system() == 'Darwin':
       candidates = ['AppleGothic', 'Apple SD Gothic Neo', 'Nanum Gothic', 'Arial Unicode MS']
   else:
       candidates = ['malgun gothic', 'gulim', 'dotum', 'batang', 'arial unicode ms']
   title_font = pygame.font.SysFont(candidates[0], 48, bold=True)   # 초기 입력 제목
   input_font = pygame.font.SysFont(candidates[0], 28)                # 초기 입력 프롬프트
   sim_font   = pygame.font.SysFont(candidates[0], 15)                # 시뮬레이션용 작은 폰트
   status_font= pygame.font.SysFont(candidates[0], 20, bold=True)       # 상태창용 (20pt)
   final_font = pygame.font.SysFont(candidates[0], 36, bold=True)       # 최종 통계 화면 (36pt)
except Exception:
   title_font  = pygame.font.SysFont(None, 48, bold=True)
   input_font  = pygame.font.SysFont(None, 28)
   sim_font    = pygame.font.SysFont(None, 15)
   status_font = pygame.font.SysFont(None, 20, bold=True)
   final_font  = pygame.font.SysFont(None, 36, bold=True)

AGV_SPEED = 1.0

GRID_COLS = SIM_WIDTH // GRID_SIZE
GRID_ROWS = SCREEN_HEIGHT // GRID_SIZE
grid_map = [[0 for _ in range(GRID_COLS)] for _ in range(GRID_ROWS)]

total_orders    = 0
items_per_order = 0
total_agvs      = 0
total_humans    = 0

charger_positions = []
exit_positions    = []
waiting_positions = []
shelf_positions   = []

time_history = []
completed_orders_history = []
completed_items_history = []

# 전역 변수: 스크롤 오프셋 (마우스휠로 조절)
region_scroll_offset = 0

# 전역 변수 agvs (나중에 참조하기 위해)
global agvs
agvs = []

# -----------------------------------------------------------
def get_agv_color(index):
   base_colors = [
       (255, 100, 100),
       (100, 255, 100),
       (100, 100, 255),
       (255, 255, 100),
       (255, 100, 255)
   ]
   if index < len(base_colors):
       return base_colors[index]
   import colorsys
   patterns = [
       (0.9, 0.8),
       (0.7, 1.0),
       (1.0, 0.6),
       (0.8, 0.9),
       (0.6, 0.7)
   ]
   pattern_index = (index // 12) % len(patterns)
   s_base, v_base = patterns[pattern_index]
   s = max(0.5, min(1.0, s_base - (index % 3) * 0.05))
   v = max(0.5, min(1.0, v_base - (index % 4) * 0.05))
   h = ((index * 0.618033988749895) % 1 + (index % 7) * 0.02) % 1
   r, g, b = colorsys.hsv_to_rgb(h, s, v)
   return (int(r*255), int(g*255), int(b*255))
# -----------------------------------------------------------

# ── Item 렌더링 캐시 ───────────────────────────────────────────
_ITEM_SURF_CACHE = {}
_FONT = pygame.font.SysFont("arial", 12)
_INV_SURF_CACHE = {}

def get_item_surface(number):
    """번호별 Surface를 캐시 재사용"""
    if number not in _ITEM_SURF_CACHE:
        surf = pygame.Surface((GRID_SIZE, GRID_SIZE), pygame.SRCALPHA)
        pygame.draw.rect(surf, ITEM_COLOR, surf.get_rect(), border_radius=4)
        txt = _FONT.render(str(number), True, BLACK)
        surf.blit(txt, txt.get_rect(center=surf.get_rect().center))
        _ITEM_SURF_CACHE[number] = surf
    return _ITEM_SURF_CACHE[number]

def get_inv_surface(inv):
    """재고 숫자 Surface를 캐시 재사용"""
    if inv not in _INV_SURF_CACHE:
        # 글씨 크기를 GRID_SIZE의 1/4로 고정 (예: GRID_SIZE=20 → 크기=5px)
        tiny_font = pygame.font.SysFont(None, max(6, GRID_SIZE // 4))
        surf = tiny_font.render(str(inv), True, (100, 100, 100))
        _INV_SURF_CACHE[inv] = surf
    return _INV_SURF_CACHE[inv]
# ───────────────────────────────────────────────────────────────

# Item 클래스 수정
class Item:
   def __init__(self, x, y, order_id):
       # 아이템 원위치 저장
       self.init_x = x
       self.init_y = y
       # 실제 좌표도 초기 위치로 설정
       self.x = self.init_x
       self.y = self.init_y
       self.order_id = order_id
       self.picked = False
       self.assigned_agv_id = None
       self.number = 0
       self.reserved_by = None  

   def draw(self, screen, offset_x, offset_y):
        # 픽업 상태에 따라 색 결정
        agv_picked = getattr(self, 'picked_by_agv', False)
        hum_picked = getattr(self, 'picked_by_human', False)
        if hum_picked:
            color = (120, 120, 255)   # 연한 파랑색 (Human 픽업)
        elif agv_picked:
            color = (180, 120, 180)   # 연한 보라색 (AGV 픽업)
        else:
            color = ITEM_COLOR      # 기본 노랑

        # 블록 그리기
        surf = pygame.Surface((GRID_SIZE, GRID_SIZE), pygame.SRCALPHA)
        pygame.draw.rect(surf, color, surf.get_rect(), border_radius=2)

        # 화면에 뿌리기
        screen.blit(
            surf,
            (self.x * GRID_SIZE + offset_x,
             self.y * GRID_SIZE + offset_y)
        )

class Order:
   def __init__(self, order_id, num_items):
       self.order_id = order_id
       self.num_items = num_items
       self.items = []
       self.agv_region = None
       logging.info(f"주문 {order_id} 생성: 아이템 {num_items}개")

   def add_item(self, item):
       self.items.append(item)

   def is_completed(self):
       return all(item.picked for item in self.items)

class AGV:
   def __init__(self, agv_id, x, y, speed=None):
       self.id = agv_id
       self.x = x
       self.y = y
       self.speed = speed if speed is not None else AGV_SPEED
       self.capacity = MAX_CAPACITY
       self.target_x = None
       self.target_y = None
       self.path = []
       self.orders = []
       self.current_item = None  # 이전 버전과의 호환성을 위해 유지
       self.current_items = []  # 새로 추가: 현재 위치의 모든 아이템
       self.current_location = None  # 새로 추가: 현재 위치
       self.current_order_index = 0
       self.state = "IDLE"
       self.path_history = []
       self.picked_items = []
       self.current_order = None
       self.total_distance = 0
       self.region_index = 0
       self.assigned_items = []
       self.action_timer = 0
       self.action_duration = 5.0
       self.total_items_processed = 0  # 총 처리 아이템 카운터 추가
       self.assigned_region = []  # 할당된 구역 추가

   def draw(self):
       pygame.draw.rect(screen, PURPLE, (self.x * GRID_SIZE, self.y * GRID_SIZE, GRID_SIZE, GRID_SIZE))
       agv_text = sim_font.render(f"A-{self.id}", True, PURPLE)
       screen.blit(agv_text, (self.x * GRID_SIZE - 5, self.y * GRID_SIZE - 15))
       if self.picked_items:
           cnt_text = sim_font.render(f"({len(self.picked_items)})", True, AGV_COUNT_COLOR)
           screen.blit(cnt_text, (self.x * GRID_SIZE - 5, self.y * GRID_SIZE + GRID_SIZE))
       for i in range(len(self.path_history) - 1):
           x1, y1 = self.path_history[i]
           x2, y2 = self.path_history[i+1]
           pygame.draw.line(
               screen, PATH_COLOR,
               (x1 * GRID_SIZE + GRID_SIZE//2, y1 * GRID_SIZE + GRID_SIZE//2),
               (x2 * GRID_SIZE + GRID_SIZE//2, y2 * GRID_SIZE + GRID_SIZE//2), 2
           )

   def assign_orders(self, orders):
       self.orders = orders
       if orders:
           self.current_order_index = 0
           self.find_next_item()

   def find_next_item(self):
       # ─── 새로운 구간 시작 시 이전 궤적 삭제 ───────────
       self.path_history = [(self.x, self.y)]

       # 위치별로 아이템 그룹화
       location_groups = self.group_items_by_location()

       # 1) 용량 한도 초과 또는 남은 아이템 없으면 배송/귀환 처리
       if len(self.picked_items) >= self.capacity or not location_groups:
           if self.picked_items:
               self.state = "MOVING_TO_EXIT"
               drop_pos = self.find_closest_exit()
               if drop_pos:  # drop_pos가 None이 아닌 경우만 처리
                   self.target_x, self.target_y = self.find_closest_accessible_point(drop_pos[0], drop_pos[1])
                   self.path = self.find_path(self.x, self.y, self.target_x, self.target_y)
               else:
                   # drop_pos가 None인 경우 적절한 처리
                   logging.warning(f"{type(self).__name__}-{self.id}: 출구를 찾을 수 없습니다. 현재 위치 유지.")
                   self.state = "DELIVERED"  # 다른 상태로 전환하거나 처리
               return True
           else:
               self.state = "RETURNING"
               return False

       # 2) A*로 계산한 경로 길이를 기준으로 가장 가까운 위치 선택
       best_location = None
       best_path = []
       best_items = []
       best_score = float('-inf')  # 최고 점수 초기화 (음의 무한대)
       weight_factor = 0  # 가중치 중요도 무시, 경로 효율성만 반영영

       # 방문한 위치별 횟수 집계
       visit_counts = {}
       for hist_x, hist_y in self.path_history:
           pos = (hist_x, hist_y)
           visit_counts[pos] = visit_counts.get(pos, 0) + 1

       for pos, items in location_groups.items():
           # 해당 위치의 재고 확인
           inventory = shelf_inventory.get(pos, 0)

           # 해당 위치에 재고가 없으면 건너뛰기 (무한 루프 방지)
           if inventory <= 0:
               logging.info(f"AGV-{self.id}: 위치 {pos}의 재고가 없어 건너뜁니다.")
               continue

           # 픽업할 아이템 수가 재고보다 많으면, 재고만큼만 처리
           pickable_items = min(len(items), inventory)
           if pickable_items <= 0:
               continue  # 픽업할 수 있는 아이템이 없으면 건너뛰기

           # 아이템 주변의 접근 가능한 점을 찾고
           tx, ty = self.find_closest_accessible_point(pos[0], pos[1])
           target_pos = (tx, ty)

           # 방문 횟수에 따른 패널티 (방문 횟수가 많을수록 우선순위 낮춤)
           visit_count = visit_counts.get(target_pos, 0)
           path_penalty = visit_count * 5  # 방문 횟수당 거리 5 추가

           # A* 경로 계산
           path = self.find_path(self.x, self.y, tx, ty)

           # 경로가 비어 있든 아니든, 길이(0 포함)로 점수 계산
           score = -len(path) - path_penalty

           # 최고 점수보다 높으면 갱신
           if score > best_score:
               best_score = score
               best_location = pos
               best_path = path
               best_items = items[:pickable_items]

       # 3) 선택된 위치가 없다면 종료
       if not best_location:
           logging.warning(f"AGV-{self.id}: 적합한 다음 위치를 찾지 못했습니다.")
           return False

       # 4) 최적 경로로 이동
       self.current_item = None  # 기존 아이템 참조 제거
       self.current_items = best_items  # 현재 위치의 모든 아이템 저장
       for it in self.current_items:     # 예약 등록
         it.reserved_by = (self.__class__.__name__, self.id)
       self.current_location = best_location  # 현재 위치 저장
       self.state = "MOVING_TO_ITEM"
       # path가 비어 있으면 이미 목표에 도달한 상태 → 현재 좌표를 타겟으로
       self.path = best_path
       if self.path:
           # 정상 경로 있을 때는 마지막 노드를 타겟으로
           self.target_x, self.target_y = self.path[-1]
       else:
           # 이미 접근 가능한 지점에 있으므로 현 위치를 목표로 설정
           self.target_x, self.target_y = self.x, self.y
       self.action_timer = 0  # 타이머 리셋

       # 선택된 위치와 아이템 수 로깅
       item_weight = best_items[0].number if best_items else 0
       agent_type = "Human" if isinstance(self, Human) else "AGV"
       logging.info(f"{agent_type}-{self.id}: 위치 {best_location}에서 {len(best_items)}개 아이템 픽업 예정, 가중치: {item_weight}, 경로 길이: {len(best_path)}")

   # AGV 클래스에 추가
   def group_items_by_location(self):
       """영역 지정 안 됐거나, 할당 영역 끝나면 전체 아이템, 아니면 내 영역 우선."""
       location_groups = {}
       region = getattr(self, 'assigned_region', [])

       # 1) 영역 할당받았고, 아직 처리할 아이템이 남아 있으면 → 내 영역만
       if region:
           # 내 영역 안의 미픽업·미예약 아이템 리스트
           region_items = [
               it for it in items
               if not it.picked
                  and (it.reserved_by is None or it.reserved_by == (self.__class__.__name__, self.id))
                  and (it.x, it.y) in region
           ]
           if region_items:
               for it in region_items:
                   pos = (it.x, it.y)
                   if pos not in location_groups:
                       location_groups[pos] = []
                   location_groups[pos].append(it)
               return location_groups

       # 2) (영역 없거나, 영역 내 처리 끝난 경우) 전체 창고 대상
       for it in items:
           if it.picked or (it.reserved_by is not None and it.reserved_by != (self.__class__.__name__, self.id)):
               continue
           pos = (it.x, it.y)
           if pos not in location_groups:
               location_groups[pos] = []
           location_groups[pos].append(it)

       return location_groups

   def find_closest_accessible_point(self, tx, ty):
       if 0 <= tx < GRID_COLS and 0 <= ty < GRID_ROWS and grid_map[ty][tx] == 0:
           return (tx, ty)
       directions = [(1,0), (-1,0)]
       md = float('inf')
       best = None
       for dx, dy in directions:
           nx, ny = tx+dx, ty+dy
           if 0 <= nx < GRID_COLS and 0 <= ny < GRID_ROWS and grid_map[ny][nx] == 0:
               d = abs(self.x - nx) + abs(self.y - ny)
               if d < md:
                   md = d
                   best = (nx, ny)
       if best:
           return best
       for yy in range(GRID_ROWS):
           for xx in range(GRID_COLS):
               if grid_map[yy][xx] == 0:
                   d = abs(tx-xx) + abs(ty-yy)
                   if d < md:
                       md = d
                       best = (xx, yy)
       return best if best else (self.x, self.y)

   def find_closest_exit(self):
      # dropoff_positions가 비어있으면 exit_positions 사용
       global dropoff_positions, exit_positions
    
       # 위치 목록 선택 (dropoff_positions이 비어있으면 exit_positions 사용)
       positions = dropoff_positions if dropoff_positions else exit_positions
    
       md = float('inf')
       best = None
       for dx, dy in positions:
           d = abs(self.x-dx) + abs(self.y-dy)
           if d < md:
              md = d
              best = (dx, dy)
       return best

   def update(self, dt):
       # DELIVERED 상태에서는 더 이상 처리하지 않음 → 경고 반복 방지
       if self.state == "DELIVERED":
            return
       global sim_time

    # sim_time이 정의되지 않았다면 0으로 초기화
       if 'sim_time' not in globals():
            global sim_time
            sim_time = 0

       if self.state in ["PICKING", "DROPPING"]:
           self.action_timer += dt
           if self.action_timer >= self.action_duration:
               if self.state == "PICKING":
                   # 현재 위치의 정보
                   pos = self.current_location
                   actual_inventory = shelf_inventory.get(pos, 0)
                   backorder = shelf_backorder.get(pos, 0)

                   # 픽업할 수 있는 아이템 수 계산 (재고, 남은 용량 중 최소값)
                   available_capacity = self.capacity - len(self.picked_items)
                   items_to_pick = min(len(self.current_items), available_capacity)

                   # 실제 가능한 픽업 수량 (재고 기준) - 부족분은 픽업하지 않음
                   actual_pickup = min(items_to_pick, actual_inventory)

                   # 부족한 수량 (재고보다 필요한 양이 더 많을 경우)
                   shortage = max(0, items_to_pick - actual_pickup)

                   if actual_pickup > 0:
                       # 실제로 픽업 가능한 아이템만 픽업
                       for item in self.current_items[:actual_pickup]:
                           item.picked = True
                           item.picked_by_agv = True
                           self.picked_items.append(item)
                           self.total_items_processed += 1

                       # 재고 감소
                       shelf_inventory[pos] = max(0, shelf_inventory[pos] - actual_pickup)
                       logging.info(f"AGV-{self.id}: 위치 {pos}에서 {actual_pickup}개 아이템 픽업, 남은 재고: {shelf_inventory[pos]}")

                   if shortage > 0:
                       # 부족분 업데이트
                       shelf_backorder[pos] += shortage
                       logging.warning(f"AGV-{self.id}: 위치 {pos}에서 {shortage}개 아이템 재고 부족, 총 부족분: {shelf_backorder[pos]}")

                       # 부족분에 해당하는 아이템들은 픽업할 수 없으므로 할당 제거
                       for item in self.current_items[actual_pickup:]:
                           if item in self.assigned_items:
                               self.assigned_items.remove(item)
                               logging.info(f"AGV-{self.id}: 재고 부족으로 아이템 할당 제거 (위치: {pos})")

                   # ── 픽업 완료 즉시 예약 해제
                   for it in self.current_items:
                       it.reserved_by = None
                   # 다음 아이템 예약 (다른 에이전트가 남은 물량을 가져갈 수 있게)
                   self.find_next_item()
                   self.action_timer = 0
                   return

               elif self.state == "DROPPING":
                   # ── 드롭오프 완료 후 손에 든 아이템 비우기
                   self.picked_items = []
                   # 상태를 IDLE로 전환 (즉시 재예약 안 함)
                   self.state = "IDLE"
                   self.action_timer = 0
                   return
           return

       # 이동 로직
       if not self.path:
           if self.state == "MOVING_TO_ITEM" and self.current_items:
               # 동일 위치에서 n개 픽업 시 unit_time * n
               num = len(self.current_items)
               self.action_duration = num * 5.0
               self.state = "PICKING"
               self.action_timer = 0
               
           elif self.state == "MOVING_TO_EXIT" and self.picked_items:
               # 드롭오프 시간 = 픽업 완료된 아이템 개수 * 5초
               num = len(self.picked_items)
               self.action_duration = num * 5.0
               # 실제 드롭오프 단계로 진입
               self.state = "DROPPING"
               self.action_timer = 0
           elif self.state == "DROPPING":
               # 드롭오프 완료 직후에만 DELIVERED 상태로 전환
               self.picked_items = []
               self.state = "DELIVERED"
               self.action_timer = 0
               return
           elif self.state == "RETURNING":
               # 귀환 완료 후에만 Delivered
               self.state = "DELIVERED"
               self.path_history = []
           else:
               # 아직 처리되지 않은 아이템이 남아 있는지 확인
               if any(not item.picked for item in items):
                   # 남아있으면 다음 아이템 예약 시도
                   success = self.find_next_item()
                   if not success:
                       logging.warning(f"{type(self).__name__}-{self.id}: 예약할 다음 아이템을 찾지 못했습니다.")
               else:
                   # 모든 아이템 처리 완료 → 귀환 모드로 전환
                   self.state = "RETURNING"

       else:  # 경로가 있으면 이동
           nx, ny = self.path[0]
           px, py = self.x, self.y
           dx = nx - self.x
           dy = ny - self.y
           if abs(dx) > 0:
               self.x += (1 if dx > 0 else -1) * self.speed * dt
           elif abs(dy) > 0:
               self.y += (1 if dy > 0 else -1) * self.speed * dt
           moved = math.hypot(self.x-px, self.y-py)
           self.total_distance += moved

           # 히트맵 데이터 업데이트: '이동 중'일 때만 누적
           try:
               if heatmap_data is not None and self.state in ["MOVING_TO_ITEM", "MOVING_TO_EXIT", "RETURNING"]:
                   update_heatmap(self.x, self.y, dt)
           except Exception as e:
               logging.warning(f"히트맵 업데이트 오류: {e}")

           if math.hypot(self.x - nx, self.y - ny) < self.speed * dt:
               self.x, self.y = nx, ny
               self.path_history.append((self.x, self.y))
               self.path.pop(0)

               # 상태 변경 감지
               if not hasattr(self, 'last_state') or self.state != getattr(self, 'last_state', None):
                   self.last_state = self.state
                   self.last_state_change_time = sim_time
   def find_path(self, sx, sy, ex, ey):
       # ── A* 경로 캐싱 초기화 ─────────────────────────────
       if not hasattr(self, '_path_cache'):
           self._path_cache = {}
       # ── 캐시 크기 제한: 5000개 초과 시 초기화 ──
       if len(self._path_cache) > 5000:
           self._path_cache.clear()
       key = (sx, sy, ex, ey)
       if key in self._path_cache:
           return self._path_cache[key]
      # ────────────────────────────────────────────────────
       if sx == ex and sy == ey:
           return []
       directions = [(0,-1), (1,0), (0,1), (-1,0)]
       open_set = []
       closed_set = set()
       came_from = {}
       g_score = {(sx, sy): 0}
       f_score = {(sx, sy): abs(sx-ex)+abs(sy-ey)}
       heapq.heappush(open_set, (f_score[(sx, sy)], (sx, sy)))
       open_nodes = {(sx, sy)}
       while open_set:
           _, current = heapq.heappop(open_set)
           open_nodes.remove(current)
           if current == (ex, ey):
               path = []
               while current in came_from:
                   path.append(current)
                   current = came_from[current]
               result = path[::-1]
               self._path_cache[key] = result
               return result
           closed_set.add(current)
           for dx, dy in directions:
               nx, ny = current[0] + dx, current[1] + dy
               if not (0 <= nx < GRID_COLS and 0 <= ny < GRID_ROWS):
                   continue
               if grid_map[ny][nx] == 1:
                   continue
               if (nx, ny) in closed_set:
                   continue
               tg = g_score[current] + 1
               if (nx, ny) not in open_nodes or tg < g_score.get((nx, ny), float('inf')):
                   came_from[(nx, ny)] = current
                   g_score[(nx, ny)] = tg
                   f_score[(nx, ny)] = tg + abs(nx-ex)+abs(ny-ey)
                   if (nx, ny) not in open_nodes:
                       heapq.heappush(open_set, (f_score[(nx, ny)], (nx, ny)))
                       open_nodes.add((nx, ny))
       # 실패 반환도 캐시에 저장
       self._path_cache[key] = []
       return []
   
# ── Human 클래스 추가 시작 ─────────────────────────────────────
class Human(AGV):
    def draw(self, screen, offset_x, offset_y):
        # Human 경로
        for i in range(len(self.path_history)-1):
            x1,y1 = self.path_history[i]
            x2,y2 = self.path_history[i+1]
            pygame.draw.line(
                screen, HUMAN_PATH_COLOR,
                (x1*GRID_SIZE+GRID_SIZE//2, y1*GRID_SIZE+GRID_SIZE//2),
                (x2*GRID_SIZE+GRID_SIZE//2, y2*GRID_SIZE+GRID_SIZE//2),
                2
            )
        # Human 본체
        cx = int(self.x * GRID_SIZE + GRID_SIZE//2)
        cy = int(self.y * GRID_SIZE + GRID_SIZE//2)
        pygame.draw.circle(screen, BLUE, (cx, cy), GRID_SIZE//2)
        id_txt = sim_font.render(f"H-{self.id}", True, BLUE)
        screen.blit(id_txt, (self.x*GRID_SIZE-5, self.y*GRID_SIZE-15))
        # 픽업 카운트
        if self.picked_items:
            cnt_txt = sim_font.render(f"({len(self.picked_items)})", True, HUMAN_COUNT_COLOR)
            screen.blit(cnt_txt, (self.x*GRID_SIZE-5, self.y*GRID_SIZE+GRID_SIZE))

    def update(self, dt):
        prev_state = self.state
        super().update(dt)
        # ── 히트맵 업데이트: '이동 중'인 경우에만 누적
        if self.state in ["MOVING_TO_ITEM", "MOVING_TO_EXIT", "RETURNING"]:
            update_heatmap(self.x, self.y, dt)
        # 픽업 완료 후 상태 전환 처리
        if prev_state == "PICKING" and self.state != "PICKING":
            for item in self.picked_items:
                item.picked_by_human = True
# ── Human 클래스 추가 끝 ──────────────────────────────────────

def draw_grid():
   for x in range(0, SIM_WIDTH, GRID_SIZE):
       pygame.draw.line(screen, (220,220,200), (x, 0), (x, SCREEN_HEIGHT))
   for y in range(0, SCREEN_HEIGHT, GRID_SIZE):
       pygame.draw.line(screen, (220,220,200), (0, y), (SIM_WIDTH, y))

def draw_shelves():
   global shelf_positions
   shelf_positions = []
   for row in range(SHELF_ROWS):
       for col in range(SHELF_COLS):
           tx = margin_x + col * (shelf_block_width + gap_x)
           ty = margin_y + row * (shelf_block_height + gap_y)
           for i in range(SHELF_UNIT_WIDTH):
               for j in range(SHELF_UNIT_HEIGHT):
                   x = tx + i * GRID_SIZE
                   y = ty + j * GRID_SIZE
                   gx, gy = x // GRID_SIZE, y // GRID_SIZE

                   # 검은색 대신 짙은 회색으로 변경
                   pygame.draw.rect(screen, (50, 50, 50), (x, y, GRID_SIZE, GRID_SIZE))

                   if 0 <= gy < len(grid_map) and 0 <= gx < len(grid_map[0]):
                       grid_map[gy][gx] = 1
                   shelf_positions.append((gx, gy))

def draw_zones():
   global charger_positions, exit_positions, waiting_positions
   charger_positions = []
   exit_positions = []
   waiting_positions = []
   ext_h = GRID_SIZE
   ext_y = SCREEN_HEIGHT - ext_h
   pygame.draw.rect(screen, RED, (0, ext_y, SIM_WIDTH, ext_h))
   for x in range(0, SIM_WIDTH, GRID_SIZE):
       pygame.draw.rect(screen, BLACK, (x, ext_y, GRID_SIZE, GRID_SIZE), 1)
       gx, gy = x // GRID_SIZE, ext_y // GRID_SIZE
       if 0 <= gy < len(grid_map) and 0 <= gx < len(grid_map[0]):
           grid_map[gy][gx] = 1
       exit_positions.append((gx, gy))
   c_w = 60 * GRID_SIZE
   c_h = GRID_SIZE
   c_x = (SIM_WIDTH - c_w) // 2
   c_x = (c_x // GRID_SIZE) * GRID_SIZE
   c_y = 0
   pygame.draw.rect(screen, GREEN, (c_x, c_y, c_w, c_h))
   for x in range(c_x, c_x+c_w, GRID_SIZE):
       pygame.draw.rect(screen, BLACK, (x, c_y, GRID_SIZE, GRID_SIZE), 1)
       gx, gy = x // GRID_SIZE, c_y // GRID_SIZE
       if 0 <= gy < len(grid_map) and 0 <= gx < len(grid_map[0]):
           grid_map[gy][gx] = 1
       charger_positions.append((gx, gy))
   w_w = GRID_SIZE
   w_h = 15 * GRID_SIZE
   w_x = 0
   w_y = (SCREEN_HEIGHT - w_h) // 2
   w_y = (w_y // GRID_SIZE) * GRID_SIZE
   pygame.draw.rect(screen, BLUE, (w_x, w_y, w_w, w_h))
   for y in range(w_y, w_y+w_h, GRID_SIZE):
       pygame.draw.rect(screen, BLACK, (w_x, y, GRID_SIZE, GRID_SIZE), 1)
       gx, gy = w_x // GRID_SIZE, y // GRID_SIZE
       if 0 <= gy < len(grid_map) and 0 <= gx < len(grid_map[0]):
           grid_map[gy][gx] = 1
       waiting_positions.append((gx, gy))

def setup_agv_regions(total_agvs, total_humans):
   global region_scroll_offset
   region_scroll_offset = 0
   instructions = [
       "Tab: 에이전트 전환 (AGV <-> Human)",
       "드래그: 구역 설정",
       "S: 속도 설정",
       "Space: 다음 에이전트 선택",
       "Enter: 완료 후 시작"
   ]
   regions = [[] for _ in range(total_agvs + total_humans)]
   speeds  = [AGV_SPEED for _ in range(total_agvs + total_humans)]
   current_agv = 0
   drawing = False
   start_pos = None
   setting_mode = "region"
   
   # 에이전트 타입 추가 (AGV 또는 Human)
   agent_type = "AGV"
   
   while True:
       for event in pygame.event.get():
           if event.type == pygame.QUIT:
               pygame.quit(); sys.exit()
           elif event.type == pygame.MOUSEWHEEL:
               region_scroll_offset -= event.y * 10
               if region_scroll_offset < 0:
                   region_scroll_offset = 0
           elif event.type == pygame.MOUSEBUTTONDOWN and event.button == 1:
               if setting_mode == "region":
                   drawing = True
                   start_pos = pygame.mouse.get_pos()
               elif setting_mode == "speed":
                   mouse_x = pygame.mouse.get_pos()[0]
                   sbx = SIM_WIDTH + 10
                   sbw = STATS_WIDTH - 20
                   if sbx <= mouse_x <= sbx + sbw:
                       rel = (mouse_x - sbx) / sbw
                       new_speed = round(max(1, min(5, rel * 5)), 1)
                       # AGV일 땐 0~total_agvs-1, Human일 땐 total_agvs~ 끝
                       idx = current_agv if agent_type=="AGV" else total_agvs + current_agv
                       speeds[idx] = new_speed
           elif event.type == pygame.MOUSEBUTTONUP and event.button == 1:
               if setting_mode == "region" and drawing:
                   drawing = False
                   end_pos = pygame.mouse.get_pos()
                   if end_pos[0] > SIM_WIDTH:
                       end_pos = (SIM_WIDTH, end_pos[1])
                   sgx = max(0, min(start_pos[0] // GRID_SIZE, GRID_COLS - 1))
                   sgy = max(0, min(start_pos[1] // GRID_SIZE, GRID_ROWS - 1))
                   egx = max(0, min(end_pos[0] // GRID_SIZE, GRID_COLS - 1))
                   egy = max(0, min(end_pos[1] // GRID_SIZE, GRID_ROWS - 1))
                   for yy in range(min(sgy, egy), max(sgy, egy) + 1):
                       for xx in range(min(sgx, egx), max(sgx, egx) + 1):
                           if 0 <= yy < len(grid_map) and 0 <= xx < len(grid_map[0]) and grid_map[yy][xx] == 1:
                               cell = (xx, yy)
                               for r in regions:
                                   if cell in r:
                                       r.remove(cell)
                               # AGV면 0…total_agvs-1, Human이면 total_agvs…total_agvs+total_humans-1
                               idx = current_agv if agent_type=="AGV" else total_agvs + current_agv
                               if cell not in regions[idx]:
                                   regions[idx].append(cell)
           elif event.type == pygame.KEYDOWN:
               if event.key == pygame.K_s:
                   setting_mode = "speed" if setting_mode == "region" else "region"
               elif event.key == pygame.K_TAB:
                   # AGV ⇄ Human 전환 시 current_agv 리셋
                   agent_type  = "Human" if agent_type=="AGV" else "AGV"
                   current_agv = 0
               elif event.key == pygame.K_SPACE:
                   # 같은 타입 내에서 다음 에이전트로
                   if agent_type=="AGV":
                       current_agv = (current_agv + 1) % total_agvs
                   else:
                       current_agv = (current_agv + 1) % total_humans
               elif event.key == pygame.K_RETURN:
                   logging.info("영역 설정 완료, 시뮬레이션 모드로 진입합니다.")
                   pygame.event.clear()
                   return regions, speeds
               
       screen.fill(WHITE)
       draw_grid(); draw_zones(); draw_shelves()
       pygame.draw.rect(screen, (240,240,240), (SIM_WIDTH, 0, STATS_WIDTH, SCREEN_HEIGHT))
       for i, reg in enumerate(regions):
           c = get_agv_color(i)
           for pos in reg:
               x, y = pos
               pygame.draw.rect(screen, c, (x*GRID_SIZE, y*GRID_SIZE, GRID_SIZE, GRID_SIZE), 1)
       if setting_mode == "region" and drawing:
           cp = pygame.mouse.get_pos()
           rect = pygame.Rect(
               min(start_pos[0], cp[0]),
               min(start_pos[1], cp[1]),
               abs(cp[0]-start_pos[0]),
               abs(cp[1]-start_pos[1])
           )
           # AGV/Human 모두 get_agv_color로 색 결정 (Human은 인덱스 오프셋)
           drag_color = (
               get_agv_color(current_agv)
               if agent_type == "AGV"
               else get_agv_color(total_agvs + current_agv)
           )
           pygame.draw.rect(screen, drag_color, rect, 2)
       if setting_mode == "speed":
           sbh = 30
           sbw = STATS_WIDTH - 20
           sbx = SIM_WIDTH + 10
           sb_y = 10
           pygame.draw.rect(screen, (200,200,200), (sbx, sb_y, sbw, sbh))
           # AGV/Human 모두 올바른 인덱스에서 속도 읽기
           idx        = current_agv if agent_type=="AGV" else total_agvs + current_agv
           curr_speed = speeds[idx]
           mark_x = sbx + (curr_speed - 1)/4 * sbw
           # 색도 AGV/Human 드래그 색과 일치
           bar_color  = (
              get_agv_color(current_agv)
              if agent_type=="AGV"
              else get_agv_color(total_agvs + current_agv)
           )
           pygame.draw.rect(screen, bar_color, (mark_x-5, sb_y-5, 10, sbh+10))
           for i in range(5):
               lx = sbx + i/4 * sbw
               pygame.draw.line(screen, BLACK, (lx, sb_y), (lx, sb_y+sbh), 2)
               lvl_surf = sim_font.render(str(i+1), True, BLACK)
               screen.blit(lvl_surf, (lx-5, sb_y+sbh+5))
           # 에이전트별 속도 텍스트도 idx 기준으로 읽기
           sp_surf = sim_font.render(
              f"{agent_type}-{current_agv+1} 속도: {curr_speed:.1f}x",
              True, BLACK
           )
           screen.blit(sp_surf, (sbx, sb_y-40))
           base_inst_y = sb_y + sbh + 20
       else:
           base_inst_y = 10
       for i, line in enumerate(instructions):
           line_surf = sim_font.render(line, True, BLUE)
           screen.blit(line_surf, (SIM_WIDTH+10, base_inst_y + i*30))
       # “현재 설정 중” 텍스트 위치 및 색 변경
       cur_y = base_inst_y + len(instructions)*30 + 20
       # drag_color와 동일하게 적용
       text_color = (
           get_agv_color(current_agv)
           if agent_type == "AGV"
           else get_agv_color(total_agvs + current_agv)
       )
       cur_info = sim_font.render(
           f"현재 설정 중: {agent_type}-{current_agv+1} "
           f"({'속도 설정' if setting_mode=='speed' else '구역 설정'})",
           True, text_color
       )
       screen.blit(cur_info, (SIM_WIDTH+10, cur_y))
       info_y = cur_y + 40
       info_title = sim_font.render(f"설정된 {agent_type} 구역 및 속도:", True, BLACK)
       screen.blit(info_title, (SIM_WIDTH+10, info_y))
       region_info_area = pygame.Rect(SIM_WIDTH+10, info_y+30, STATS_WIDTH-20, 150)
       pygame.draw.rect(screen, (230,230,230), region_info_area)
       pygame.draw.rect(screen, BLACK, region_info_area, 1)
       content_lines = []
       
       # 현재 에이전트 타입에 따라 AGV/Human 구역 개수 표시 (항상 리스트에 나옴)
       if agent_type == "AGV":
           for idx in range(total_agvs):
               cnt = len(regions[idx])
               content_lines.append(f"AGV-{idx+1}: {cnt} 선반, 속도: {speeds[idx]}")
       else:  # Human 타입
           for idx in range(total_humans):
               cnt = len(regions[total_agvs + idx])
               content_lines.append(
                   f"Human-{idx+1}: {cnt} 선반, 속도: {speeds[total_agvs+idx]}"
               )
       
       content_height = len(content_lines) * 25
       scroll_surface = pygame.Surface((region_info_area.width-20, max(content_height, region_info_area.height-20)))
       scroll_surface.fill((230,230,230))
       for idx, line in enumerate(content_lines):
           # AGV면 idx, Human이면 total_agvs+idx 색상 사용
           color = (
              get_agv_color(idx)
              if agent_type == "AGV"
              else get_agv_color(total_agvs + idx)
           )
           txt = status_font.render(line, True, color)
           scroll_surface.blit(txt, (0, idx*25))
       screen.blit(scroll_surface, (region_info_area.x+10, region_info_area.y+10),
                   area=pygame.Rect(0, region_scroll_offset, region_info_area.width-20, region_info_area.height-20))
       pygame.display.flip()
       clock.tick(30)
   return regions, speeds

# ── Human 영역 및 속도 설정 (AGV 함수 재활용) ─────────────────────────
def setup_human_regions(total_agvs, total_humans):
    """
    Human 영역 설정: setup_agv_regions을 호출해
    구역(regions)과 속도(speeds)를 함께 받아옵니다.
    """
    regions, speeds = setup_agv_regions(total_agvs, total_humans)
    pygame.event.clear()
    pygame.time.delay(200)  # 200ms 지연
    logging.info("Human 영역 설정 완료")

    # AGV 뒤쪽에 붙은 human 파트만 슬라이스
    human_regions = regions[total_agvs:]
    human_speeds  = speeds[total_agvs:]
    return human_regions, human_speeds
# ───────────────────────────────────────────────────────────────

def get_simulation_input():
   box_w, box_h = 250, 50
   input_boxes = [
        pygame.Rect(SCREEN_WIDTH//2 - box_w//2, SCREEN_HEIGHT//2 - 160, box_w, box_h),
        pygame.Rect(SCREEN_WIDTH//2 - box_w//2, SCREEN_HEIGHT//2 -  80, box_w, box_h),
        pygame.Rect(SCREEN_WIDTH//2 - box_w//2, SCREEN_HEIGHT//2 +   0, box_w, box_h),
        pygame.Rect(SCREEN_WIDTH//2 - box_w//2, SCREEN_HEIGHT//2 +  80, box_w, box_h)
   ]
   prompts = [
        "주문 수 (1-10000):",
        "주문당 아이템 수 (1-100):",
        "AGV 대수 (0-60):",
        "Human 대수 (0-60):"
    ]
   inputs = ["", "", "", ""]
   active_box = None

   # 랜덤 아이템 체크박스 추가
   checkbox_rect = pygame.Rect(SCREEN_WIDTH//2 - box_w//2, SCREEN_HEIGHT//2 + 140, 20, 20)
   random_items = False
   random_item_count = None

   while True:
       for event in pygame.event.get():
           if event.type == pygame.QUIT:
               pygame.quit(); sys.exit()
           elif event.type == pygame.MOUSEBUTTONDOWN:
               pos = pygame.mouse.get_pos()
               # 입력 상자 체크
               for i, box in enumerate(input_boxes):
                   if box.collidepoint(pos):
                       # 랜덤 아이템이 선택된 경우 주문당 아이템 수 입력 상자는 비활성화
                       if i == 1 and random_items:
                           continue
                       active_box = i
                       break
               # 체크박스 체크
               if checkbox_rect.collidepoint(pos):
                   random_items = not random_items
                   if random_items:
                       # 랜덤 모드 켜질 때마다 새 값 생성
                       random_item_count = random.randint(1, 100)
                       # 입력창 비활성화
                       if active_box == 1:
                           active_box = None
                       # inputs[1]에도 표시해 둠
                       inputs[1] = str(random_item_count)
                   else:
                       # 랜덤 해제 시 초기화
                       inputs[1] = ""
                       random_item_count = None
           elif event.type == pygame.KEYDOWN:
               if event.key == pygame.K_TAB:
                   if active_box is None:
                       active_box = 0
                   else:
                       # 랜덤 아이템이 선택된 경우 주문당 아이템 수 입력 상자는 건너뜀
                       if random_items:
                           active_box = 2 if active_box == 0 else 0
                       else:
                           active_box = (active_box + 1) % len(input_boxes)
               elif active_box is not None:
                   if event.key == pygame.K_RETURN:
                       # 입력 검증
                       valid_input = True
                       if not inputs[0].strip():  # 주문 수는 필수
                           valid_input = False
                       if not random_items and not inputs[1].strip():  # 랜덤이 아닐 경우 주문당 아이템 수는 필수
                           valid_input = False
                       if not inputs[2].strip():  # AGV 대수는 필수
                           valid_input = False

                       if valid_input:
                           try:
                               tot = int(inputs[0])
                               itm = int(inputs[1]) if not random_items else random_item_count
                               agv = int(inputs[2])
                               human = int(inputs[3])

                               # 값 범위 제한
                               tot   = max(1, min(10000, tot))
                               itm   = max(1, min(100, itm))
                               agv   = max(0, min(60, agv))
                               human = max(0, min(60, human))

                               # 둘 다 0이면 오류로 간주하고 재입력 요구
                               if agv == 0 and human == 0:
                                   logging.error("AGV와 Human을 모두 0으로 설정할 수 없습니다. 하나는 최소 1 이상이어야 합니다.")
                                   show_error_message("AGV와 Human 중 최소 하나는 1 이상이어야 합니다. 다시 입력해주세요")
                                   valid_input = False
                               else:
                                  return tot, itm, agv, human, random_items
                           except:
                               pass
                   elif event.key == pygame.K_BACKSPACE:
                       inputs[active_box] = inputs[active_box][:-1]
                   else:
                       if event.unicode.isdigit():
                           inputs[active_box] += event.unicode

       screen.fill(WHITE)
       title_surf = title_font.render("시뮬레이션 설정 입력", True, BLACK)
       screen.blit(title_surf, (SCREEN_WIDTH//2 - title_surf.get_width()//2, SCREEN_HEIGHT//2 - 260))

       for i, box in enumerate(input_boxes):
           # 랜덤 아이템이 선택된 경우 주문당 아이템 수 입력 상자는 회색으로 비활성화
           if i == 1 and random_items:
               pygame.draw.rect(screen, (200,200,200), box)  # 회색으로 표시
           else:
               pygame.draw.rect(screen, (230,230,230), box)

           pygame.draw.rect(screen, BLACK, box, 2)
           prompt_surf = input_font.render(prompts[i], True, BLACK)
           screen.blit(prompt_surf, (box.x - prompt_surf.get_width() - 10,
                                   box.y + (box.height - prompt_surf.get_height()) // 2))

           # 랜덤 아이템이 선택된 경우 주문당 아이템 수 입력 상자에는 "랜덤 (1-100)" 표시
           if i == 1 and random_items:
               if random_item_count is not None:
                   text = f"{random_item_count} (랜덤)"    # 실제 뽑힌 값 표시
                   text_color = BLACK
               else:
                   text = "랜덤 (1-100)"
                   text_color = (100,100,100)
           else:
               text = inputs[i]
               text_color = BLACK

           in_surf = input_font.render(text, True, text_color)
           screen.blit(in_surf, (box.x+5, box.y + (box.height - in_surf.get_height()) // 2))

       # 체크박스 그리기
       pygame.draw.rect(screen, (230,230,230), checkbox_rect)
       pygame.draw.rect(screen, BLACK, checkbox_rect, 2)
       if random_items:
           # 체크 표시 그리기
           pygame.draw.line(screen, BLACK,
                           (checkbox_rect.x + 3, checkbox_rect.y + checkbox_rect.height//2),
                           (checkbox_rect.x + 8, checkbox_rect.y + checkbox_rect.height - 5), 2)
           pygame.draw.line(screen, BLACK,
                           (checkbox_rect.x + 8, checkbox_rect.y + checkbox_rect.height - 5),
                           (checkbox_rect.x + checkbox_rect.width - 3, checkbox_rect.y + 5), 2)

       # 체크박스 라벨
       checkbox_label = input_font.render("주문당 아이템 수 랜덤 (1-100)", True, BLACK)
       screen.blit(checkbox_label, (checkbox_rect.x + checkbox_rect.width + 10,
                                 checkbox_rect.y + (checkbox_rect.height - checkbox_label.get_height())//2))

       guide_surf = input_font.render("모든 값을 입력 후 Enter 키를 눌러 시작", True, BLACK)
       screen.blit(guide_surf, (
           SCREEN_WIDTH//2 - guide_surf.get_width()//2,
           SCREEN_HEIGHT//2 + 200
       ))

       pygame.display.flip()
       clock.tick(30)

def generate_items(orders, agv_regions, human_regions):
   items = []
   global shelf_inventory, shelf_backorder

   # 모든 선반 위치에 재고 초기화
   for pos in shelf_positions:
       shelf_inventory[pos] = 500
       shelf_backorder[pos] = 0

   # 선반 위치별 주문 수량 추적
   location_order_counts = {}
   
   # AGV + Human 영역 풀 생성 - 비어있을 경우 전체 선반 사용
   all_regions = []
   for reg in agv_regions:
       if reg:  # 비어있지 않은 영역만 추가
           all_regions.extend(reg)
   for reg in human_regions:
       if reg:  # 비어있지 않은 영역만 추가
           all_regions.extend(reg)
   
   # 영역이 전부 비어있으면 전체 선반 사용
   target_positions = list(set(all_regions)) if all_regions else shelf_positions

   for od in orders:
       for _ in range(od.num_items):
           if target_positions:
               # 사용 가능한 위치에서 랜덤 선택
               pos = random.choice(target_positions)
               
               # 해당 위치의 주문 수량 추적
               if pos not in location_order_counts:
                   location_order_counts[pos] = 0
               location_order_counts[pos] += 1
               
               # 주문 수량이 재고를 초과하는지 확인
               if location_order_counts[pos] > 500:
                   shelf_backorder[pos] = max(shelf_backorder[pos], location_order_counts[pos] - 500)
                   logging.warning(f"위치 {pos}의 주문 수량({location_order_counts[pos]})이 재고(500)를 초과했습니다. 부족분: {shelf_backorder[pos]}")
               
               # 아이템 생성
               x, y = pos
               it = Item(x, y, od.order_id)
               it.number = 1
               od.add_item(it)
               items.append(it)
               
   logging.info(f"총 {len(items)}개 아이템 생성 완료")
   return items

def create_agvs(num_agvs):
   agvs = []
   for i in range(num_agvs):
       if charger_positions:
           sx, sy = charger_positions[i % len(charger_positions)]
           agv = AGV(i+1, sx, sy)
           agv.region_index = i
           agvs.append(agv)
   return agvs

def draw_progress_bar(screen, x, y, width, height, progress, color):
   """진행률 막대 그래프 그리기"""
   # 배경 (회색)
   pygame.draw.rect(screen, (200, 200, 200), (x, y, width, height))
   # 진행률 (색상)
   fill_width = int(width * progress / 100)
   if fill_width > 0:  # 0보다 클 때만 그리기
       pygame.draw.rect(screen, color, (x, y, fill_width, height))
   # 테두리
   pygame.draw.rect(screen, BLACK, (x, y, width, height), 1)
   # 텍스트
   text = sim_font.render(f"{progress:.1f}%", True, BLACK)
   text_x = x + width // 2 - text.get_width() // 2
   text_y = y + height // 2 - text.get_height() // 2
   screen.blit(text, (text_x, text_y))

def draw_line_graph(screen, x, y, width, height, times, values, color, max_value=None, title=""):
   """시간에 따른 데이터 선 그래프 그리기"""
   if not times or not values or len(times) < 2 or len(values) < 2:
       # 데이터가 없거나 충분하지 않으면 그리지 않음
       return

   # 배경
   pygame.draw.rect(screen, (240, 240, 240), (x, y, width, height))
   pygame.draw.rect(screen, BLACK, (x, y, width, height), 1)

   # 제목
   title_text = sim_font.render(title, True, BLACK)
   screen.blit(title_text, (x + 5, y + 5))

   # 축 그리기 (여백 고려)
   margin_left = 30
   margin_bottom = 20
   margin_top = 30

   # 축 그리기
   pygame.draw.line(screen, BLACK, (x + margin_left, y + height - margin_bottom),
                   (x + width - 10, y + height - margin_bottom), 2)  # X축
   pygame.draw.line(screen, BLACK, (x + margin_left, y + height - margin_bottom),
                   (x + margin_left, y + margin_top), 2)  # Y축

   # 값 범위 계산
   max_time = max(times)
   if max_value is None:
       max_value = max(values) if values else 1
   if max_value == 0:
       max_value = 1

   # 선 그래프 그리기
   points = []
   for i in range(len(times)):
       px = x + margin_left + ((times[i] / max_time) * (width - margin_left - 10))
       py = y + height - margin_bottom - ((values[i] / max_value) * (height - margin_top - margin_bottom))
       points.append((int(px), int(py)))
       pygame.draw.circle(screen, color, (int(px), int(py)), 3)

   if len(points) > 1:
       pygame.draw.lines(screen, color, False, points, 2)

   # Y축 눈금 (3개)
   for i in range(4):
       mark_y = y + height - margin_bottom - (i / 3) * (height - margin_top - margin_bottom)
       pygame.draw.line(screen, BLACK, (x + margin_left - 5, mark_y), (x + margin_left, mark_y), 1)
       value = int(max_value * (i / 3))
       value_text = sim_font.render(str(value), True, BLACK)
       screen.blit(value_text, (x + 5, mark_y - value_text.get_height() // 2))

   # X축 눈금 (3개)
   for i in range(4):
       mark_x = x + margin_left + (i / 3) * (width - margin_left - 10)
       pygame.draw.line(screen, BLACK, (mark_x, y + height - margin_bottom),
                       (mark_x, y + height - margin_bottom + 5), 1)
       time_value = int(max_time * (i / 3))
       time_text = sim_font.render(str(time_value), True, BLACK)
       screen.blit(time_text, (mark_x - time_text.get_width() // 2, y + height - margin_bottom + 5))

def draw_pie_chart(screen, x, y, radius, values, colors, labels=None):
   """파이 차트 그리기"""
   if not values or sum(values) == 0:
       return

   total = sum(values)
   start_angle = 0
   
   pie_font = pygame.font.SysFont(None, max(8, int(sim_font.get_height() * 0.8)))
   label_positions = []

   for i, value in enumerate(values):
       # 각도 계산 (라디안)
       angle = 2 * math.pi * (value / total)
       end_angle = start_angle + angle

       # 색상
       color = colors[i] if i < len(colors) else (100, 100, 100)

       # 부채꼴 그리기
       points = [(x, y)]  # 중심점
       segments = 20  # 부드러움 정도
       for j in range(segments+1):
           segment_angle = start_angle + (end_angle - start_angle) * (j / segments)
           px = x + radius * math.cos(segment_angle)
           py = y + radius * math.sin(segment_angle)
           points.append((int(px), int(py)))

       pygame.draw.polygon(screen, color, points)

       # 테두리
       pygame.draw.lines(screen, BLACK, False, points[1:], 1)

       # 레이블 (있는 경우)
       if labels and i < len(labels) and value / total > 0.05:  # 비율이 5% 이상인 경우만
           label_angle = start_angle + angle / 2
           label_x = x + (radius * 0.5) * math.cos(label_angle)
           label_y = y + (radius * 0.5) * math.sin(label_angle)

           label_text = pie_font.render(labels[i], True, BLACK)
           label_positions.append((label_text, label_x, label_y))

       # 다음 부채꼴 시작 각도
       start_angle = end_angle

   # 레이블을 파이 조각 위에 한 번에 그려서 항상 앞에 표시
   for label_text, lx, ly in label_positions:
    screen.blit(label_text, (
       int(lx - label_text.get_width()//2),
       int(ly - label_text.get_height()//2)
   ))

def draw_stats(agvs, orders, sim_time):
   comp = sum(1 for od in orders if od.is_completed())
   tot = len(orders)
   percent = (comp / tot * 100) if tot > 0 else 0

   total_items = sum(od.num_items for od in orders)
   picked_items = sum(sum(1 for item in od.items if item.picked) for od in orders)
   percent_picked = (picked_items / total_items * 100) if total_items > 0 else 0

   # 상태 색상 정의를 함수 시작 부분으로 이동
   state_colors = {
       "IDLE": (150,150,150),      # 회색
       "PICKING": (100,200,100),   # 초록색
       "MOVING": (200,200,100),    # 노란색 
       "DROPPING": (200,100,100),  # 빨간색
       "DELIVERED": (100,100,200)  # 파란색
   }

   stats_height = 200
   stats_rect = pygame.Rect(SIM_WIDTH+10, 10, STATS_WIDTH-20, stats_height)
   pygame.draw.rect(screen, (240,240,240), stats_rect)
   pygame.draw.rect(screen, BLACK, stats_rect, 2)
   title_text = status_font.render("시뮬레이션 상태", True, BLACK)
   screen.blit(title_text, (stats_rect.x+10, stats_rect.y+10))

   # 기본 정보
   time_text = status_font.render(f"경과 시간: {sim_time:.1f}초", True, BLACK)
   screen.blit(time_text, (stats_rect.x+10, stats_rect.y+40))
   speed_text = status_font.render(f"배속: {simulation_speed:.1f}x", True, BLACK)
   screen.blit(speed_text, (stats_rect.x+10, stats_rect.y+70))
   adjust_text = status_font.render("A: +0.1, Z: -0.1", True, BLACK)
   screen.blit(adjust_text, (stats_rect.x+10, stats_rect.y+100))

   # 주문 완료 정보
   order_text = status_font.render(f"주문 완료: {comp}/{tot} ({percent:.1f}%)", True, BLACK)
   screen.blit(order_text, (stats_rect.x+10, stats_rect.y+130))

   # 아이템 처리 정보
   items_text = status_font.render(f"아이템 처리: {picked_items}/{total_items} ({percent_picked:.1f}%)", True, BLACK)
   screen.blit(items_text, (stats_rect.x+10, stats_rect.y+160))

   # 효율성 지표
   efficiency_y = stats_rect.y + stats_height + 10
   efficiency_rect = pygame.Rect(SIM_WIDTH+10, efficiency_y, STATS_WIDTH-20, 90)
   pygame.draw.rect(screen, (230,230,230), efficiency_rect)
   pygame.draw.rect(screen, BLACK, efficiency_rect, 1)

   eff_title = status_font.render("효율성 지표:", True, BLACK)
   screen.blit(eff_title, (efficiency_rect.x+10, efficiency_y+10))

   # AGV 가동률
   if agvs:
       active_count = sum(1 for a in agvs if a.state not in ["IDLE", "DELIVERED"])
       total_agvs_count = len(agvs)
       active_ratio = active_count / total_agvs_count * 100

       agv_ratio_text = status_font.render(f"AGV 가동률: {active_ratio:.1f}%", True, BLACK)
       screen.blit(agv_ratio_text, (efficiency_rect.x+10, efficiency_y+35))

   # 처리 속도 (초당 아이템 처리 수)
   if sim_time > 0:
       items_per_second = picked_items / sim_time
       speed_text = status_font.render(f"처리 속도: {items_per_second:.2f}개/초", True, BLACK)
       screen.blit(speed_text, (efficiency_rect.x+10, efficiency_y+60))

   # 그래프 시작 위치
   graph_y = efficiency_y + 100

   # 진행률 그래프
   progress_rect = pygame.Rect(SIM_WIDTH+10, graph_y, STATS_WIDTH-20, 80)
   pygame.draw.rect(screen, (230,230,230), progress_rect)
   pygame.draw.rect(screen, BLACK, progress_rect, 1)

   progress_title = status_font.render("진행률 그래프:", True, BLACK)
   screen.blit(progress_title, (progress_rect.x+10, graph_y+10))

   # 주문 진행률 막대 그래프
   order_label = sim_font.render("주문:", True, BLACK)
   screen.blit(order_label, (progress_rect.x+10, graph_y+35))
   draw_progress_bar(screen, progress_rect.x+60, graph_y+35, progress_rect.width-80, 15, percent, (0, 150, 0))

   # 아이템 진행률 막대 그래프
   item_label = sim_font.render("아이템:", True, BLACK)
   screen.blit(item_label, (progress_rect.x+10, graph_y+55))
   draw_progress_bar(screen, progress_rect.x+60, graph_y+55, progress_rect.width-80, 15, percent_picked, (0, 100, 200))

   # ── AGV & Human 상태 파이 차트 (옆으로 나란히) ─────────────────────────
   pie_y   = graph_y + 90
   chart_w = (STATS_WIDTH - 30) // 2   # 좌우 여백 30px
   chart_h = 160                       # 높이를 160으로 증가 (수정)

   # — AGV 차트 —
   if agvs:
       agv_rect = pygame.Rect(SIM_WIDTH+10, pie_y, chart_w, chart_h)
       pygame.draw.rect(screen, (230,230,230), agv_rect)
       pygame.draw.rect(screen, BLACK, agv_rect, 1)
       title = status_font.render("AGV 상태", True, BLACK)
       tx = agv_rect.x + (agv_rect.width  - title.get_width())  // 2
       ty = agv_rect.y + 10
       screen.blit(title, (tx, ty))

       # 상태 목록을 미리 정의하여 순서 고정 (추가)
       state_order = ["IDLE", "PICKING", "MOVING", "DROPPING", "DELIVERED"]
    
       agv_states = {
           "IDLE":      sum(1 for a in agvs if a.state=="IDLE"),
           "PICKING":   sum(1 for a in agvs if a.state=="PICKING"),
           "MOVING":    sum(1 for a in agvs if a.state in ["MOVING_TO_ITEM","MOVING_TO_EXIT","RETURNING"]),
           "DROPPING":  sum(1 for a in agvs if a.state=="DROPPING"),
           "DELIVERED": sum(1 for a in agvs if a.state=="DELIVERED")
       }
       vals = []
       labs = []
       cols = []  # 색상 리스트 별도 생성
       
       for state in state_order:
           if state in agv_states and agv_states[state] > 0:
               vals.append(agv_states[state])
               labs.append(state)
               cols.append(state_colors[state])  # 미리 정의된 색상 사용

       if vals:
           cx = agv_rect.x + agv_rect.width//2
           cy = agv_rect.y + chart_h//2 + 25
           r  = min(chart_w, chart_h)//2 - 15  # 반지름 더 크게: -20에서 -15으로 수정
           draw_pie_chart(screen, cx, cy, r, vals, cols, labs)

   # — Human 차트 —
   if 'humans' in globals() and humans:
       hum_rect = pygame.Rect(SIM_WIDTH+20+chart_w, pie_y, chart_w, chart_h)
       pygame.draw.rect(screen, (230,230,230), hum_rect)
       pygame.draw.rect(screen, BLACK, hum_rect, 1)
       htitle = status_font.render("Human 상태", True, BLACK)
       tx = hum_rect.x + (hum_rect.width - htitle.get_width()) // 2
       ty = hum_rect.y + 10
       screen.blit(htitle, (tx, ty))
    
       # 상태 목록을 미리 정의하여 순서 고정 (추가)
       state_order = ["IDLE", "PICKING", "MOVING", "DROPPING", "DELIVERED"]
       
       human_states = {
           "IDLE":      sum(1 for h in humans if h.state=="IDLE"),
           "PICKING":   sum(1 for h in humans if h.state=="PICKING"),
           "MOVING":    sum(1 for h in humans if h.state in ["MOVING_TO_ITEM","MOVING_TO_EXIT","RETURNING"]),
           "DROPPING":  sum(1 for h in humans if h.state=="DROPPING"),
           "DELIVERED": sum(1 for h in humans if h.state=="DELIVERED")
       }
       hvals = []
       hlabs = []
       hcols = []  # Human 색상 리스트
       
       for state in state_order:
           if state in human_states and human_states[state] > 0:
               hvals.append(human_states[state])
               hlabs.append(state)
               hcols.append(state_colors[state])  # AGV와 동일한 색상 매핑 사용
       if hvals:
           hcx = hum_rect.x + hum_rect.width//2
           hcy = hum_rect.y + chart_h//2 + 25
           hr  = min(chart_w, chart_h)//2 - 15  # 반지름 더 크게: -20에서 -15으로 수정
           draw_pie_chart(screen, hcx, hcy, hr, hvals, hcols, hlabs)

   # ── 선 그래프 위치 아래로 이동 ────────────────────────────────────────
   line_y = pie_y + chart_h + 10

   # 시간별 처리량 선 그래프 (데이터가 있는 경우)
   if 'time_points' in globals() and 'completed_orders_points' in globals() and len(time_points) > 1:
       #line_y = pie_y + 120 if agvs else graph_y + 90
       line_rect = pygame.Rect(SIM_WIDTH+10, line_y, STATS_WIDTH-20, 150)
       pygame.draw.rect(screen, (230,230,230), line_rect)
       pygame.draw.rect(screen, BLACK, line_rect, 1)

       line_title = status_font.render("시간별 처리량:", True, BLACK)
       screen.blit(line_title, (line_rect.x+10, line_y+10))

       try:
           # 시간-주문 그래프
           draw_line_graph(screen, line_rect.x+10, line_y+40, line_rect.width-20, 100,
                         time_points, completed_orders_points, (0, 100, 200),
                         max_value=tot, title="완료 주문 수")
       except Exception as e:
           error_text = sim_font.render(f"그래프 오류: {str(e)}", True, RED)
           screen.blit(error_text, (line_rect.x+10, line_y+50))

def final_screen(agvs, orders, sim_time):
   """향상된 최종 통계 화면"""
   global time_points, completed_orders_points, completed_items_points
   global items  # items 변수 추가
   global heatmap_data  # 히트맵 데이터 추가

   # 통계 계산
   tot_time = sim_time
   tot_dist = sum(a.total_distance for a in agvs)
   avg_dist = tot_dist / len(agvs) if agvs else 0

   # 전체 주문 및 아이템 통계
   total_orders_count = len(orders)
   completed_orders_count = sum(1 for od in orders if od.is_completed())
   total_items_count = sum(od.num_items for od in orders)
   completed_items_count = sum(sum(1 for item in od.items if item.picked) for od in orders)

   # 각 AGV별 통계 계산
   temp_agv_stats = []
   for a in agvs:
       # 이 AGV가 픽업한 아이템 수
       picked_items = a.total_items_processed

       # 이 AGV가 담당한 주문 중 완료된 주문 수 계산
       completed_orders = 0

       # 모든 주문을 순회
       for od in orders:
           # 주문의 모든 아이템이 이 AGV에 할당되었는지 확인
           order_items_by_this_agv = sum(1 for item in od.items if item.assigned_agv_id == a.id)

           # 주문의 모든 아이템이 처리되었고, 그 중 하나 이상이 이 AGV에 할당되었다면
           if od.is_completed() and order_items_by_this_agv > 0:
               completed_orders += 1

       # 할당된 아이템 수 계산
       assigned_items_count = sum(1 for it in items if it.assigned_agv_id == a.id)

       # 아이템당 이동 거리 계산 (낮을수록 효율적)
       distance_per_item = a.total_distance / picked_items if picked_items > 0 else float('inf')

       temp_agv_stats.append({
           'id': a.id,
           'picked_items': picked_items,
           'completed_orders': completed_orders,
           'total_distance': a.total_distance,
           'distance_per_item': distance_per_item,  # 아이템당 이동 거리 저장
           'assigned_items': assigned_items_count
       })

   # 가장 효율적인 AGV 찾기 (아이템당 이동 거리가 가장 적은 AGV)
   valid_agvs = [a for a in temp_agv_stats if a['picked_items'] > 0]
   if valid_agvs:
       best_efficiency = min(a['distance_per_item'] for a in valid_agvs)
   else:
       best_efficiency = 1.0  # 모든 AGV가 아이템을 처리하지 않았을 경우 기본값

   # 백분율 효율성 계산 및 최종 통계 저장
   agv_stats = []
   for a in temp_agv_stats:
       if a['picked_items'] > 0:
           # 백분율 효율성 계산 (가장 효율적인 AGV가 100%)
           efficiency_percent = (best_efficiency / a['distance_per_item']) * 100.0
       else:
           efficiency_percent = 0.0

       # 최종 통계에 백분율 효율성과 원래 값 둘 다 추가
       agv_stats.append({
           'id': a['id'],
           'picked_items': a['picked_items'],
           'completed_orders': a['completed_orders'],
           'total_distance': a['total_distance'],
           'efficiency': efficiency_percent,  # 백분율 효율성
           'distance_per_item': a['distance_per_item'],  # 원래 값(아이템당 이동 거리) 추가
           'assigned_items': a['assigned_items']
       })

   # ── Human 통계 계산 (추가) ────────────────────────────────────────────
   temp_human_stats = []
   for h in humans:
       # 이 Human이 픽업한 아이템 수
       picked_items = h.total_items_processed

       # 이 Human이 담당한 주문 중 완료된 주문 수 계산
       completed_orders = 0
       for od in orders:
           reserved_by_human = sum(
               1
               for item in od.items
               if getattr(item, 'assigned_human_id', None) == h.id
           )
           if od.is_completed() and reserved_by_human > 0:
                completed_orders += 1

       total_dist = h.total_distance
       dist_per_item = total_dist / picked_items if picked_items > 0 else float('inf')
       assigned_items_count = sum(
           1
           for it in items
           if getattr(it, 'assigned_human_id', None) == h.id
       )
       temp_human_stats.append({
           'id': h.id,
           'picked_items': picked_items,
           'completed_orders': completed_orders,
           'total_distance': total_dist,
           'distance_per_item': dist_per_item,
           'assigned_items': assigned_items_count
       })

   valid_humans = [x for x in temp_human_stats if x['picked_items'] > 0]
   if valid_humans:
       best_hum_eff = min(x['distance_per_item'] for x in valid_humans)
   else:
       best_hum_eff = 1.0

   human_stats = []
   for x in temp_human_stats:
       if x['picked_items'] > 0:
           efficiency_percent = (best_hum_eff / x['distance_per_item']) * 100.0
       else:
           efficiency_percent = 0.0

       human_stats.append({
           'id': x['id'],
           'picked_items': x['picked_items'],
           'completed_orders': x['completed_orders'],
           'total_distance': x['total_distance'],
           'efficiency': efficiency_percent,
           'distance_per_item': x['distance_per_item'],
           'assigned_items': x['assigned_items']
       })
   # ───────────────────────────────────────────────────────────────────────

   # 메인 통계 화면 무한 루프
   scroll_offset = 0  # 스크롤 오프셋 변수

   # 탭 관련 변수
   current_tab = 0  # 0: 종합 통계, 1: AGV 통계, 2: Human 통계, 3: 주문 처리 그래프, 4: 경로 히트맵
   tab_names = ["종합 통계", "AGV 통계", "Human 통계", "주문 처리 그래프", "경로 히트맵"]

   while True:
       for event in pygame.event.get():
           if event.type == pygame.QUIT:
               pygame.quit(); sys.exit()
           if event.type == pygame.KEYDOWN:
               if event.key == pygame.K_RETURN:
                   return
               elif event.key == pygame.K_s:  # S키로 스크린샷 저장
                   timestamp = time.strftime("%Y%m%d-%H%M%S")
                   pygame.image.save(screen, f"statistics_{timestamp}.png")
                   print(f"통계 스크린샷이 저장되었습니다: statistics_{timestamp}.png")
               elif event.key == pygame.K_LEFT:  # 탭 전환 (좌)
                   current_tab = (current_tab - 1) % len(tab_names)
                   scroll_offset = 0  # 탭 변경 시 스크롤 초기화
               elif event.key == pygame.K_RIGHT:  # 탭 전환 (우)
                   current_tab = (current_tab + 1) % len(tab_names)
                   scroll_offset = 0  # 탭 변경 시 스크롤 초기화
           elif event.type == pygame.MOUSEWHEEL:
               # 스크롤 조정 (마우스 휠)
               scroll_offset -= event.y * 30
               scroll_offset = max(0, scroll_offset)  # 음수 방지

       # 화면 초기화
       screen.fill(WHITE)

       # 상단 제목 표시
       title_text = final_font.render("시뮬레이션 최종 통계", True, (0,100,0))
       screen.blit(title_text, (SCREEN_WIDTH//2 - title_text.get_width()//2, 30))

       # 탭 메뉴 그리기
       tab_width = SCREEN_WIDTH // len(tab_names)
       for i, tab_name in enumerate(tab_names):
           tab_rect = pygame.Rect(i * tab_width, 100, tab_width, 50)
           tab_color = (180, 230, 180) if i == current_tab else (220, 220, 220)
           pygame.draw.rect(screen, tab_color, tab_rect)
           pygame.draw.rect(screen, BLACK, tab_rect, 1)

           tab_text = status_font.render(tab_name, True, BLACK)
           screen.blit(tab_text, (tab_rect.centerx - tab_text.get_width()//2,
                                 tab_rect.centery - tab_text.get_height()//2))

       # 현재 탭 콘텐츠 영역
       content_rect = pygame.Rect(50, 170, SCREEN_WIDTH - 100, SCREEN_HEIGHT - 220)
       pygame.draw.rect(screen, (240, 240, 240), content_rect)
       pygame.draw.rect(screen, BLACK, content_rect, 1)

       # 각 탭별 내용 표시
       if current_tab == 0:  # 종합 통계
           # 텍스트 정보 - 좌측
           stats_y = content_rect.y + 20
           left_x = content_rect.x + 20

           # 기본 통계 정보
           stats_info = [
               f"총 작업 시간: {tot_time:.1f}초",
               f"AGV 평균 이동 거리: {avg_dist:.1f}",
               f"처리된 주문: {completed_orders_count}/{total_orders_count} ({completed_orders_count/total_orders_count*100:.1f}%)",
               f"처리된 아이템: {completed_items_count}/{total_items_count} ({completed_items_count/total_items_count*100:.1f}%)",
               f"초당 처리 아이템: {completed_items_count/tot_time:.2f}개/초",
               f"사용된 AGV 수: {len(agvs)}대"
           ]

           for i, info in enumerate(stats_info):
               info_text = status_font.render(info, True, BLACK)
               screen.blit(info_text, (left_x, stats_y + i * 40))

           # 그래프 - 우측 (진행률 막대 그래프)
           graph_x = content_rect.x + content_rect.width // 2 + 20
           graph_y = stats_y
           graph_w = content_rect.width // 2 - 40

           # 주문 진행률
           progress_label = status_font.render("주문 처리율:", True, BLACK)
           screen.blit(progress_label, (graph_x, graph_y))
           draw_progress_bar(screen, graph_x, graph_y + 30, graph_w, 30,
                           completed_orders_count/total_orders_count*100, (0, 150, 0))

           # 아이템 진행률
           item_label = status_font.render("아이템 처리율:", True, BLACK)
           screen.blit(item_label, (graph_x, graph_y + 80))
           draw_progress_bar(screen, graph_x, graph_y + 110, graph_w, 30,
                          completed_items_count/total_items_count*100, (0, 100, 200))

           # AGV 효율성 요약 (상위/하위)
           if agv_stats:
               eff_y = graph_y + 160
               eff_label = status_font.render("AGV 효율성 요약:", True, BLACK)
               screen.blit(eff_label, (graph_x, eff_y))

               # 효율성 기준 정렬 (높을수록 효율적)
               sorted_agvs = sorted(agv_stats, key=lambda x: x['efficiency'], reverse=True)

               # 상위 3개 (있는 경우)
               for i in range(min(3, len(sorted_agvs))):
                   a = sorted_agvs[i]
                   if a['picked_items'] > 0:  # 아이템을 픽업한 AGV만
                       eff_text = status_font.render(
                           f"AGV-{a['id']}: 효율성 {a['efficiency']:.1f}% ({a['distance_per_item']:.1f} 거리/아이템), 아이템 {a['picked_items']}개",
                           True, (0, 120, 0))
                       screen.blit(eff_text, (graph_x + 20, eff_y + 30 + i * 25))

       elif current_tab == 1:  # AGV 통계
           # AGV가 0대인 경우 처리
           if not agv_stats:
               # AGV가 없을 경우 메시지 표시
               no_data_text = status_font.render("이 시뮬레이션에서는 AGV를 사용하지 않았습니다.", True, BLACK)
               screen.blit(no_data_text, (content_rect.centerx - no_data_text.get_width()//2,
                                        content_rect.centery - no_data_text.get_height()//2))
           else:
               # 스크롤 가능한 영역 준비
               scroll_surface = pygame.Surface((content_rect.width - 20, max(len(agvs) * 80 + 60, content_rect.height)))
               scroll_surface.fill((240, 240, 240))

               # 열 제목
               header_y = 10
               col_width = scroll_surface.get_width() // 5
               headers = ["AGV ID", "처리 주문", "처리 아이템", "이동 거리", "효율성"]

               for i, header in enumerate(headers):
                   header_text = status_font.render(header, True, BLACK)
                   scroll_surface.blit(header_text, (i * col_width + col_width//2 - header_text.get_width()//2, header_y))
                   # 구분선
                   if i > 0:
                       pygame.draw.line(scroll_surface, (200, 200, 200),
                                       (i * col_width, 0),
                                       (i * col_width, scroll_surface.get_height()), 1)

               # 구분선 (헤더와 내용 사이)
               pygame.draw.line(scroll_surface, BLACK, (0, header_y + 30),
                              (scroll_surface.get_width(), header_y + 30), 1)

               # AGV별 데이터
               for i, stat in enumerate(agv_stats):
                   row_y = header_y + 40 + i * 60

                   # 효율성 색상 (높을수록 녹색, 낮을수록 빨간색)
                   efficiency_color = (0, 150, 0) if stat['picked_items'] > 0 else BLACK
                   if stat['picked_items'] > 0:
                       # 효율성은 0-100% 사이의 값
                       norm_eff = max(0, min(1, stat['efficiency'] / 100.0))
                       r = min(255, int((1 - norm_eff) * 255))
                       g = min(255, int(norm_eff * 255))
                       efficiency_color = (r, g, 0)

                   # 각 열 데이터
                   agv_id_text = status_font.render(f"AGV-{stat['id']}", True, BLACK)
                   orders_text = status_font.render(f"{stat['completed_orders']}개", True, BLACK)
                   items_text = status_font.render(f"{stat['picked_items']}개", True, BLACK)
                   dist_text = status_font.render(f"{stat['total_distance']:.1f}", True, BLACK)

                   # 효율성을 백분율과 원래 값 함께 표시
                   if stat['picked_items'] > 0:
                       # 백분율 및 원래 값(아이템당 이동 거리) 둘 다 표시
                       eff_text = status_font.render(
                           f"{stat['efficiency']:.1f}%",
                           True, efficiency_color)

                       # 원래 값 작은 글자로 아래에 표시
                       dist_per_item_text = status_font.render(
                           f"({stat['distance_per_item']:.1f} 거리/아이템)",
                           True, (80, 80, 80))
                   else:
                       eff_text = status_font.render("N/A", True, BLACK)
                       dist_per_item_text = sim_font.render("", True, BLACK)

                   # 각 열에 텍스트 배치
                   scroll_surface.blit(agv_id_text, (col_width//2 - agv_id_text.get_width()//2, row_y))
                   scroll_surface.blit(orders_text, (col_width + col_width//2 - orders_text.get_width()//2, row_y))
                   scroll_surface.blit(items_text, (2*col_width + col_width//2 - items_text.get_width()//2, row_y))
                   scroll_surface.blit(dist_text, (3*col_width + col_width//2 - dist_text.get_width()//2, row_y))

                   # 효율성 표시 (백분율)
                   scroll_surface.blit(eff_text, (4*col_width + col_width//2 - eff_text.get_width()//2, row_y - 8))

                   # 아이템당 이동 거리 표시 (원래 값)
                   scroll_surface.blit(dist_per_item_text,
                                   (4*col_width + col_width//2 - dist_per_item_text.get_width()//2, row_y + 15))

                   # 행 구분선
                   pygame.draw.line(scroll_surface, (200, 200, 200),
                                   (0, row_y + 40),
                                   (scroll_surface.get_width(), row_y + 40), 1)

                   # 할당된 아이템 정보 (더 작은 글씨로 추가)
                   assigned_text = sim_font.render(f"할당된 아이템: {stat['assigned_items']}개", True, (80, 80, 80))
                   scroll_surface.blit(assigned_text, (col_width//2, row_y + 25))

               # 스크롤된 영역을 메인 화면에 표시
               screen.blit(scroll_surface, (content_rect.x + 10, content_rect.y + 10),
                          (0, scroll_offset, content_rect.width - 20, content_rect.height - 20))

               # 스크롤바 (필요한 경우)
               if scroll_surface.get_height() > content_rect.height - 20:
                   scrollbar_height = (content_rect.height - 20) * (content_rect.height - 20) / scroll_surface.get_height()
                   scrollbar_pos = scroll_offset * (content_rect.height - 20) / scroll_surface.get_height()
                   scrollbar_rect = pygame.Rect(
                       content_rect.x + content_rect.width - 10,
                       content_rect.y + 10 + scrollbar_pos,
                       5, scrollbar_height)
                   pygame.draw.rect(screen, (150, 150, 150), scrollbar_rect)

       # Human 통계 (추가)
       elif current_tab == 2:
           # Human이 0명인 경우 처리
           if not human_stats:
               # Human이 없을 경우 메시지 표시
               no_data_text = status_font.render("이 시뮬레이션에서는 Human을 사용하지 않았습니다.", True, BLACK)
               screen.blit(no_data_text, (content_rect.centerx - no_data_text.get_width()//2,
                                        content_rect.centery - no_data_text.get_height()//2))
           else:
               # Human이 있는 경우에만 통계 표시
               # 스크롤 가능한 영역 준비
               scroll_surface = pygame.Surface(
                   (content_rect.width - 20,
                    max(len(human_stats) * 80 + 60, content_rect.height))
               )
               scroll_surface.fill((240, 240, 240))

               # 열 제목
               header_y = 10
               col_width = scroll_surface.get_width() // 5
               headers = ["Human ID", "처리 주문", "처리 아이템", "이동 거리", "효율성"]
               for i, header in enumerate(headers):
                   header_text = status_font.render(header, True, BLACK)
                   scroll_surface.blit(
                       header_text,
                       (i * col_width + col_width//2 - header_text.get_width()//2,
                        header_y)
                   )
                   if i > 0:
                       pygame.draw.line(
                           scroll_surface,
                           (200, 200, 200),
                           (i * col_width, 0),
                           (i * col_width, scroll_surface.get_height()),
                           1
                       )

               # 구분선
               pygame.draw.line(
                   scroll_surface,
                   BLACK,
                   (0, header_y + 30),
                   (scroll_surface.get_width(), header_y + 30),
                   1
               )

               # Human별 데이터
               for idx, stat in enumerate(human_stats):
                   row_y = header_y + 40 + idx * 60
                   efficiency_color = (0, 150, 0) if stat['picked_items'] > 0 else BLACK
                   if stat['picked_items'] > 0:
                       norm_eff = max(0, min(1, stat['efficiency'] / 100.0))
                       r = min(255, int((1 - norm_eff) * 255))
                       g = min(255, int(norm_eff * 255))
                       efficiency_color = (r, g, 0)

                   human_id_text  = status_font.render(f"Human-{stat['id']}", True, BLACK)
                   orders_text    = status_font.render(f"{stat['completed_orders']}개", True, BLACK)
                   items_text     = status_font.render(f"{stat['picked_items']}개", True, BLACK)
                   dist_text      = status_font.render(f"{stat['total_distance']:.1f}", True, BLACK)
                   eff_text       = status_font.render(f"{stat['efficiency']:.1f}%", True, efficiency_color)
                   dist_item_text = status_font.render(
                       f"({stat['distance_per_item']:.1f} 거리/아이템)", True, (100,100,100)
                   )

                   scroll_surface.blit(
                       human_id_text,
                       (col_width//2 - human_id_text.get_width()//2, row_y)
                   )
                   scroll_surface.blit(
                       orders_text,
                       (col_width + col_width//2 - orders_text.get_width()//2, row_y)
                   )
                   scroll_surface.blit(
                       items_text,
                       (2*col_width + col_width//2 - items_text.get_width()//2, row_y)
                   )
                   scroll_surface.blit(
                       dist_text,
                       (3*col_width + col_width//2 - dist_text.get_width()//2, row_y)
                   )
                   scroll_surface.blit(
                       eff_text,
                       (4*col_width + col_width//2 - eff_text.get_width()//2, row_y-8)
                   )
                   scroll_surface.blit(
                       dist_item_text,
                       (4*col_width + col_width//2 - dist_item_text.get_width()//2, row_y+15)
                   )

                   # 행 구분선 및 할당 아이템 정보
                   pygame.draw.line(
                       scroll_surface,
                       (200,200,200),
                       (0, row_y + 40),
                       (scroll_surface.get_width(), row_y + 40),
                       1
                   )
                   assigned_text = sim_font.render(
                       f"할당된 아이템: {stat['assigned_items']}개", True, (80,80,80)
                   )
                   scroll_surface.blit(assigned_text, (col_width//2, row_y + 25))

               # 화면에 표시
               screen.blit(
                   scroll_surface,
                   (content_rect.x + 10, content_rect.y + 10),
                   (0, scroll_offset, content_rect.width - 20, content_rect.height - 20)
               )

               # 스크롤바 (필요한 경우)
               if scroll_surface.get_height() > content_rect.height - 20:
                   scrollbar_height = (content_rect.height - 20) * (content_rect.height - 20) / scroll_surface.get_height()
                   scrollbar_pos = scroll_offset * (content_rect.height - 20) / scroll_surface.get_height()
                   scrollbar_rect = pygame.Rect(
                       content_rect.x + content_rect.width - 10,
                       content_rect.y + 10 + scrollbar_pos,
                       5, scrollbar_height)
                   pygame.draw.rect(screen, (150, 150, 150), scrollbar_rect)

       elif current_tab == 3:  # 주문 처리 그래프
           if time_points and completed_orders_points and completed_items_points:
               # 그래프 영역 정의
               graph_margin = 40
               graph_width = content_rect.width - 2 * graph_margin
               graph_height = (content_rect.height - 60) // 2

               # 주문 처리 그래프
               orders_y = content_rect.y + 10
               orders_title = status_font.render("시간에 따른 주문 처리량", True, BLACK)
               screen.blit(orders_title, (content_rect.centerx - orders_title.get_width()//2, orders_y))

               draw_line_graph(screen,
                             content_rect.x + graph_margin,
                             orders_y + 30,
                             graph_width,
                             graph_height,
                             time_points,
                             completed_orders_points,
                             (0, 150, 0),
                             max_value=total_orders_count,
                             title="")

               # 아이템 처리 그래프
               items_y = orders_y + graph_height + 30
               items_title = status_font.render("시간에 따른 아이템 처리량", True, BLACK)
               screen.blit(items_title, (content_rect.centerx - items_title.get_width()//2, items_y))

               draw_line_graph(screen,
                             content_rect.x + graph_margin,
                             items_y + 30,
                             graph_width,
                             graph_height,
                             time_points,
                             completed_items_points,
                             (0, 100, 200),
                             max_value=total_items_count,
                             title="")
           else:
               # 데이터가 없는 경우 메시지
               no_data_text = status_font.render("그래프를 표시할 데이터가 없습니다.", True, BLACK)
               screen.blit(no_data_text, (content_rect.centerx - no_data_text.get_width()//2,
                                        content_rect.centery - no_data_text.get_height()//2))

       elif current_tab == 4:  # 경로 히트맵
           # 히트맵 그리기
           if heatmap_data is not None:
               draw_heatmap(screen, content_rect)
           else:
               # 히트맵 데이터가 없는 경우 메시지
               no_data_text = status_font.render("히트맵 데이터가 없습니다.", True, BLACK)
               screen.blit(no_data_text, (content_rect.centerx - no_data_text.get_width()//2,
                                        content_rect.centery - no_data_text.get_height()//2))

               info_text = sim_font.render("히트맵 데이터는 시뮬레이션 중 AGV의 이동 경로를 추적하여 생성됩니다.", True, BLACK)
               screen.blit(info_text, (content_rect.centerx - info_text.get_width()//2,
                                     content_rect.centery - info_text.get_height()//2 + 30))

       # 하단 안내 텍스트
       guide_text = status_font.render("Enter: 종료 | S: 스크린샷 저장 | ←/→: 탭 전환 | 마우스 휠: 스크롤", True, BLACK)
       screen.blit(guide_text, (SCREEN_WIDTH//2 - guide_text.get_width()//2, SCREEN_HEIGHT - 35))

       pygame.display.flip()
       clock.tick(30)

def initialize_heatmap():
   """히트맵 데이터 초기화"""
   global heatmap_data
   heatmap_data = [[0 for _ in range(GRID_COLS)] for _ in range(GRID_ROWS)]

def update_heatmap(x, y, delta_time):
   """히트맵 데이터 업데이트 (실제 경과 시간 delta_time 만큼 누적)"""
   global heatmap_data
   gx, gy = int(x), int(y)
   if 0 <= gx < GRID_COLS and 0 <= gy < GRID_ROWS:
       # 실제 시뮬레이션 시간만큼만 누적
       heatmap_data[gy][gx] += delta_time

def draw_heatmap(screen, rect):
    """히트맵 그리기 - 크기 축소 및 가운데 정렬"""
    global heatmap_data
    if heatmap_data is None:
        return

    # 최대값 찾기 (색상 강도 정규화를 위해)
    max_value = 1
    for row in heatmap_data:
        max_value = max(max_value, max(row))

    # 타이틀과 설명을 위한 공간 확보
    top_margin = 70  # 상단 여백 (제목과 설명을 위한 공간)

    # 히트맵 표시 영역 크기 계산 (원본보다 축소)
    display_width = min(rect.width - 40, SIM_WIDTH * 0.85)  # 85%로 축소
    display_height = min(rect.height - top_margin - 20, SCREEN_HEIGHT * 0.85)  # 85%로 축소

    # 축소 비율 계산
    scale_x = display_width / SIM_WIDTH
    scale_y = display_height / SCREEN_HEIGHT

    # 화면에 맞추기 위해 더 작은 비율 선택 (비율 유지)
    scale = min(scale_x, scale_y)

    # 실제 표시 크기
    actual_width = SIM_WIDTH * scale
    actual_height = SCREEN_HEIGHT * scale

    # 히트맵 표면 생성 (원본 크기)
    heatmap_surface = pygame.Surface((SIM_WIDTH, SCREEN_HEIGHT), pygame.SRCALPHA)

    # 각 격자에 대해 통과 빈도에 따라 색상 강도 결정
    for y in range(GRID_ROWS):
        for x in range(GRID_COLS):
            value = heatmap_data[y][x]
            if value > 0:
                # 통과 빈도에 따라 색상 강도 계산 (0.1 ~ 0.8 사이의 알파값)
                alpha = min(210, int(50 + (value / max_value) * 160))

                # 색상: 초록(낮은 빈도) ~ 노랑 ~ 빨강(높은 빈도)
                if value < max_value * 0.3:
                    color = (0, 255, 0, alpha)  # 초록
                elif value < max_value * 0.7:
                    color = (255, 255, 0, alpha)  # 노랑
                else:
                    color = (255, 0, 0, alpha)  # 빨강

                # 격자 그리기
                pygame.draw.rect(heatmap_surface, color, (x * GRID_SIZE, y * GRID_SIZE, GRID_SIZE, GRID_SIZE))

    # 선반 그리기
    for pos in shelf_positions:
        x, y = pos
        pygame.draw.rect(heatmap_surface, (100, 100, 100, 150), (x * GRID_SIZE, y * GRID_SIZE, GRID_SIZE, GRID_SIZE))

    # 범례 그리기
    legend_width = 200
    legend_height = 50
    legend_x = rect.x + rect.width - legend_width - 20
    legend_y = rect.y + 20

    # 색상 그라데이션
    gradient_width = legend_width - 40
    gradient_height = 20
    gradient_x = legend_x + 20
    gradient_y = legend_y + 15

    for i in range(gradient_width):
        ratio = i / gradient_width
        if ratio < 0.3:
            color = (0, 255, 0)  # 초록
        elif ratio < 0.7:
            # 초록 -> 노랑 그라데이션
            g = 255
            r = int(255 * ((ratio - 0.3) / 0.4))
            color = (r, g, 0)
        else:
            # 노랑 -> 빨강 그라데이션
            r = 255
            g = int(255 * (1 - (ratio - 0.7) / 0.3))
            color = (r, g, 0)

        pygame.draw.line(screen, color, (gradient_x + i, gradient_y), (gradient_x + i, gradient_y + gradient_height))

    # 범례 텍스트
    low_text = sim_font.render("낮음", True, BLACK)
    high_text = sim_font.render("높음", True, BLACK)
    screen.blit(low_text, (gradient_x, gradient_y + gradient_height + 5))
    screen.blit(high_text, (gradient_x + gradient_width - high_text.get_width(), gradient_y + gradient_height + 5))

    # 히트맵 제목
    title_text = status_font.render("AGV & Human 이동 경로 히트맵 (병목 구간 분석)", True, BLACK)
    screen.blit(title_text, (rect.centerx - title_text.get_width()//2, rect.y + 10))

    # 설명 텍스트
    info_text = sim_font.render("색상 강도는 AGV & Human 통과 빈도를 나타냅니다. 빨간색 구간은 병목 지점입니다.", True, BLACK)
    screen.blit(info_text, (rect.centerx - info_text.get_width()//2, rect.y + 40))

    # 축소된 히트맵을 화면 중앙에 배치
    # 원본 크기의 surface를 축소하여 화면에 표시
    scaled_surface = pygame.transform.scale(heatmap_surface, (int(actual_width), int(actual_height)))

    # 중앙 정렬 위치 계산
    center_x = rect.x + (rect.width - actual_width) // 2
    center_y = rect.y + top_margin + (rect.height - top_margin - actual_height) // 2

    # 히트맵 화면에 표시
    screen.blit(scaled_surface, (center_x, center_y))

def optimize_order_route_with_astar(order, agv, st_pos, ex_pos):
   return order.items

def optimize_order_route(order, st_pos, ex_pos):
   return order.items

def get_simulation_mode():
   """시뮬레이션 모드를 선택하는 화면 표시"""
   button_width, button_height = 300, 100
   visual_button = pygame.Rect(SCREEN_WIDTH//2 - button_width - 20, SCREEN_HEIGHT//2 - button_height//2, button_width, button_height)
   fast_button = pygame.Rect(SCREEN_WIDTH//2 + 20, SCREEN_HEIGHT//2 - button_height//2, button_width, button_height)

   # 이벤트 큐 비우기 추가
   pygame.event.clear()

   logging.info("시뮬레이션 모드 선택 화면 표시")
   while True:
       events = pygame.event.get()  # 이벤트를 변수에 저장
       for event in events:
           if event.type == pygame.QUIT:
               pygame.quit(); sys.exit()
           elif event.type == pygame.MOUSEBUTTONDOWN:
               pos = pygame.mouse.get_pos()
               if visual_button.collidepoint(pos):
                   logging.info("시각적 시뮬레이션 모드 선택됨")
                   return "VISUAL"
               elif fast_button.collidepoint(pos):
                   logging.info("고속 시뮬레이션 모드 선택됨")
                   return "FAST"

       screen.fill(WHITE)
       title_surf = title_font.render("시뮬레이션 모드 선택", True, BLACK)
       screen.blit(title_surf, (SCREEN_WIDTH//2 - title_surf.get_width()//2, SCREEN_HEIGHT//2 - 150))

       # 시각적 시뮬레이션 버튼
       pygame.draw.rect(screen, (200, 230, 200), visual_button)
       pygame.draw.rect(screen, BLACK, visual_button, 2)
       visual_text = input_font.render("시각적 시뮬레이션", True, BLACK)
       screen.blit(visual_text, (visual_button.x + visual_button.width//2 - visual_text.get_width()//2,
                                 visual_button.y + visual_button.height//2 - visual_text.get_height()//2))
       visual_desc = sim_font.render("진행 과정을 시각적으로 확인", True, BLACK)
       screen.blit(visual_desc, (visual_button.x + visual_button.width//2 - visual_desc.get_width()//2,
                                 visual_button.y + visual_button.height//2 + 20))

       # 고속 시뮬레이션 버튼
       pygame.draw.rect(screen, (230, 200, 200), fast_button)
       pygame.draw.rect(screen, BLACK, fast_button, 2)
       fast_text = input_font.render("고속 시뮬레이션", True, BLACK)
       screen.blit(fast_text, (fast_button.x + fast_button.width//2 - fast_text.get_width()//2,
                              fast_button.y + fast_button.height//2 - fast_text.get_height()//2))
       fast_desc = sim_font.render("시각화 없이 빠른 결과 도출", True, BLACK)
       screen.blit(fast_desc, (fast_button.x + fast_button.width//2 - fast_desc.get_width()//2,
                              fast_button.y + fast_button.height//2 + 20))

       pygame.display.flip()
       clock.tick(30)

def run_simulation_fast(agvs, humans, orders, items):
   """시뮬레이션을 시각적 렌더링 없이 빠르게 실행하고 결과 반환"""
   global sim_time # 전역 변수로 설정하여 AGV의 update 메서드에서 접근 가능하게 함
   global FAST_MODE
   FAST_MODE = True
   initialize_heatmap()
   dt = 1.0 / 30.0 
   sim_time = 0
   
   # ① 시각 모드처럼 시작 위치도 한 번 쌓아주기
   for a in agvs: update_heatmap(a.x, a.y, dt)
   for h in humans: update_heatmap(h.x, h.y, dt)
   
   record_interval = 5
   last_record_time = 0

   # 시간 제한 및 안전 장치
   max_simulation_time = float('inf')  # 무한대로 설정
   start_real_time = time.time()  # 실행 시작 시간 기록
   max_real_time = float('inf')  # 무한대로 설정
   max_iterations = float('inf')  # 무한대로 설정 (또는 매우 큰 정수값)

   # 진행 상태 표시
   progress = 0
   print("시뮬레이션 고속 실행 중...")

   # 데이터 기록용 변수
   time_points = []
   completed_orders_points = []
   completed_items_points = []
   last_data_record = 0

   # 각 AGV의 경로 히스토리 기록을 위한 변수
   for a in agvs:
       a.path_history = []  # 시각화를 위해 경로 히스토리 초기화

   # 시뮬레이션이 끝날 때까지 반복
   iteration_count = 0
   max_iterations = 1000000  # 최대 반복 횟수 (안전 장치)

   try:
        while True:
            # 1) 반복 및 시뮬레이션 시간 업데이트
            iteration_count += 1
            sim_time += dt

            # 2) 에이전트 업데이트
            for a in agvs:
                a.update(dt)
            for h in humans:
                h.update(dt)

            # 3) 10초 간격으로 데이터 기록
            if sim_time - last_data_record >= record_interval:
                completed_orders = sum(1 for od in orders if od.is_completed())
                completed_items  = sum(
                    sum(1 for item in od.items if item.picked)
                    for od in orders
                )
                time_points.append(sim_time)
                completed_orders_points.append(completed_orders)
                completed_items_points.append(completed_items)
                last_data_record = sim_time

            # 4) 모든 주문 완료 + 모든 에이전트 배송 완료 시 종료
            if (all(od.is_completed() for od in orders)
                and all(a.state=="DELIVERED" for a in agvs)
                and all(h.state=="DELIVERED" for h in humans)):
                logging.info("고속 시뮬레이션 완료: 모든 주문이 처리되었습니다.")
                break

            # 5) 안전장치: 최대 반복 수 초과 시 경고 후 종료
            if iteration_count > max_iterations:
                logging.warning(f"고속 시뮬레이션 안전장치({max_iterations}회) 초과, 강제 종료합니다.")
                break

            # 6) 상태 감시 및 종료
            if iteration_count % 10000 == 0:
                active_agvs   = sum(1 for a in agvs    if a.state != "DELIVERED")
                active_humans = sum(1 for h in humans if h.state != "DELIVERED")
                if active_agvs + active_humans > 0:
                    logging.info(f"진행 중: AGV {active_agvs}대, Human {active_humans}대 활성 상태")
                else:
                    # 주문이 모두 처리된 경우에만 정상 종료
                    if all(od.is_completed() for od in orders):
                        logging.info("모든 주문이 처리되어 시뮬레이션을 종료합니다.")
                        break
                    else:
                        logging.error("에이전트가 모두 DELIVERED 상태지만, 아직 처리되지 않은 주문이 존재합니다!")
                        # break 대신 continue로 루프 유지하거나, 예외를 던져 디버깅할 수도 있습니다.
                        # continue    

   except Exception as e:
       logging.error(f"고속 시뮬레이션 중 오류 발생: {e}")
       import traceback
       logging.error(traceback.format_exc())

   print(f"시뮬레이션 완료! (시간: {sim_time:.1f}초, 반복: {iteration_count})")

   # 결과 통계 계산
   completed_orders = sum(1 for od in orders if od.is_completed())
   completed_items = sum(sum(1 for item in od.items if item.picked) for od in orders)
   total_orders = len(orders)
   total_items = sum(od.num_items for od in orders)

   logging.info(f"최종 결과: 주문 {completed_orders}/{total_orders} 완료 ({completed_orders/total_orders*100:.1f}%), "
               f"아이템 {completed_items}/{total_items} 처리 ({completed_items/total_items*100:.1f}%)")

   # 결과 반환
   return {
       'sim_time': sim_time,
       'total_distance': sum(a.total_distance for a in agvs),
       'avg_distance': sum(a.total_distance for a in agvs) / len(agvs) if agvs else 0,
       'completed_orders': completed_orders,
       'total_orders': total_orders,
       'completed_items': completed_items,
       'total_items': total_items,
       'time_points': time_points,
       'completed_orders_points': completed_orders_points,
       'completed_items_points': completed_items_points,
       'iterations': iteration_count
   }

def show_visual_result(agvs, humans, orders, items, sim_time):
   """고속 시뮬레이션 후 최종 상태를 시각적으로 표시"""
   # 아이템이 원래 선반에 그려지도록 위치 복원
   for it in items:
       it.x = it.init_x
       it.y = it.init_y
   waiting = True

   while waiting:
       for event in pygame.event.get():
           if event.type == pygame.QUIT:
               pygame.quit(); sys.exit()
           if event.type == pygame.KEYDOWN:
               if event.key == pygame.K_RETURN:
                   waiting = False
               elif event.key == pygame.K_s:  # S키를 눌러 스크린샷 저장
                   timestamp = time.strftime("%Y%m%d-%H%M%S")
                   pygame.image.save(screen, f"simulation_result_{timestamp}.png")
                   print(f"스크린샷이 저장되었습니다: simulation_result_{timestamp}.png")

       # 시뮬레이션 화면 그리기
       screen.fill(WHITE)
       draw_grid()
       draw_zones()
       draw_shelves()

       # 아이템 그리기
       for it in items:
            it.draw(screen, 0, 0)

       # AGV와 경로 그리기
       for a in agvs:
           a.draw()  # 이 함수는 path_history를 사용하여 경로를 그림
       
       # Human 그리기
       for h in humans:
           h.draw(screen, margin_x, margin_y)

       # 상태창 그리기
       pygame.draw.rect(screen, (240,240,240), (SIM_WIDTH, 0, STATS_WIDTH, SCREEN_HEIGHT))
       draw_stats(agvs, orders, sim_time)

       # 추가 정보 텍스트
       info_text = status_font.render("시뮬레이션 완료 - Enter: 계속, S: 스크린샷 저장", True, BLACK)
       info_rect = info_text.get_rect(center=(SIM_WIDTH//2, SCREEN_HEIGHT - 30))
       screen.blit(info_text, info_rect)

       pygame.display.flip()
       clock.tick(30)
##엑셀 코드

def select_file_pygame():
   """PyGame 기반 파일 탐색기 (Excel 및 CSV 지원)"""
   # 초기 경로 설정
   import platform

   if platform.system() == 'Windows':
       current_path = "C:/"
   else:  # macOS 또는 Linux
       current_path = os.path.expanduser("~")

   path_history = []  # 경로 히스토리 (뒤로 가기 기능)

   font = status_font  # 상태 폰트 사용
   small_font = sim_font  # 시뮬레이션 폰트 사용

   scroll_offset = 0
   selected_index = 0

   while True:
       for event in pygame.event.get():
           if event.type == pygame.QUIT:
               pygame.quit(); sys.exit()
           elif event.type == pygame.KEYDOWN:
               if event.key == pygame.K_ESCAPE:
                   return None  # 취소
               elif event.key == pygame.K_BACKSPACE:
                   # 상위 디렉토리로 이동
                   if len(path_history) > 0:
                       current_path = path_history.pop()
                       scroll_offset = 0
                       selected_index = 0
                   else:
                       parent_dir = os.path.dirname(current_path)
                       if parent_dir and parent_dir != current_path:
                           path_history.append(current_path)
                           current_path = parent_dir
                           scroll_offset = 0
                           selected_index = 0
               elif event.key == pygame.K_UP:
                   selected_index = max(0, selected_index - 1)
                   # 스크롤 조정
                   if selected_index < scroll_offset:
                       scroll_offset = selected_index
               elif event.key == pygame.K_DOWN:
                   # 목록 항목 수에 따라 최대 인덱스 설정
                   try:
                       items = list_directory(current_path)
                       max_index = len(items) - 1
                       selected_index = min(max_index, selected_index + 1)
                       # 스크롤 조정
                       visible_items = 15  # 화면에 표시할 항목 수
                       if selected_index >= scroll_offset + visible_items:
                           scroll_offset = selected_index - visible_items + 1
                   except:
                       pass
               elif event.key == pygame.K_RETURN:
                   try:
                       items = list_directory(current_path)
                       if 0 <= selected_index < len(items):
                           item_name, is_dir = items[selected_index]
                           full_path = os.path.join(current_path, item_name)

                           if is_dir:
                               # 디렉토리인 경우 해당 디렉토리로 이동
                               path_history.append(current_path)
                               current_path = full_path
                               scroll_offset = 0
                               selected_index = 0
                           else:
                               # 파일인 경우 확장자 확인
                               if item_name.lower().endswith(('.xlsx', '.xls', '.csv')):  # CSV 추가
                                   return full_path
                               else:
                                   # 지원하지 않는 파일 형식 알림
                                   temp_surface = pygame.Surface((300, 100), pygame.SRCALPHA)
                                   temp_surface.fill((200, 200, 200, 220))
                                   msg = small_font.render("지원하지 않는 파일 형식입니다.", True, BLACK)
                                   msg2 = small_font.render("Excel(.xlsx, .xls) 또는 CSV(.csv) 파일만 지원합니다.", True, BLACK)
                                   temp_surface.blit(msg, (150 - msg.get_width()//2, 30))
                                   temp_surface.blit(msg2, (150 - msg2.get_width()//2, 60))
                                   screen.blit(temp_surface, (SCREEN_WIDTH//2 - 150, SCREEN_HEIGHT//2 - 50))
                                   pygame.display.flip()
                                   pygame.time.wait(2000)
                   except Exception as e:
                       logging.error(f"파일/디렉토리 접근 오류: {e}")
           elif event.type == pygame.MOUSEWHEEL:
               scroll_offset = max(0, scroll_offset - event.y * 3)
           elif event.type == pygame.MOUSEBUTTONDOWN:
               # 마우스 클릭 처리
               try:
                   items = list_directory(current_path)
                   mouse_y = event.pos[1]

                   # 뒤로 가기 버튼 클릭 확인
                   back_button = pygame.Rect(50, 95, 40, 30)
                   if back_button.collidepoint(event.pos):
                       if len(path_history) > 0:
                           current_path = path_history.pop()
                           scroll_offset = 0
                           selected_index = 0
                       continue

                   # 리스트 영역 클릭 확인
                   list_rect = pygame.Rect(100, 130, SCREEN_WIDTH - 200, SCREEN_HEIGHT - 230)
                   if list_rect.collidepoint(event.pos):
                       item_index = (mouse_y - list_rect.y - 5) // 30 + scroll_offset
                       if 0 <= item_index < len(items):
                           # 더블 클릭 처리 (단, PyGame에서는 기본 더블 클릭 감지가 없음)
                           selected_index = item_index
                           if event.button == 1:
                               item_name, is_dir = items[selected_index]
                               full_path = os.path.join(current_path, item_name)

                               if event.button == 1 and pygame.time.get_ticks() - getattr(event, 'last_click_time', 0) < 500:
                                   # 더블 클릭으로 간주 (500ms 이내 두 번째 클릭)
                                   if is_dir:
                                       # 디렉토리인 경우 해당 디렉토리로 이동
                                       path_history.append(current_path)
                                       current_path = full_path
                                       scroll_offset = 0
                                       selected_index = 0
                                   else:
                                       # 파일인 경우 확장자 확인
                                       if item_name.lower().endswith(('.xlsx', '.xls', '.csv')):  # CSV 추가
                                           return full_path
                               elif event.button == 1:
                                   # 싱글 클릭 저장
                                   event.last_click_time = pygame.time.get_ticks()
               except:
                   pass

       screen.fill(WHITE)

       # 제목
       title_text = font.render("파일 선택", True, BLACK)
       screen.blit(title_text, (SCREEN_WIDTH//2 - title_text.get_width()//2, 50))

       # 현재 경로 표시
       path_text = small_font.render(f"현재 경로: {current_path}", True, BLACK)
       screen.blit(path_text, (100, 100))

       # 뒤로 가기 버튼
       back_button = pygame.Rect(50, 95, 40, 30)
       pygame.draw.rect(screen, (200, 200, 200), back_button)
       pygame.draw.rect(screen, BLACK, back_button, 2)
       back_text = small_font.render("←", True, BLACK)
       screen.blit(back_text, (back_button.x + back_button.width//2 - back_text.get_width()//2,
                              back_button.y + back_button.height//2 - back_text.get_height()//2))

       # 파일/디렉토리 목록 영역
       list_rect = pygame.Rect(100, 130, SCREEN_WIDTH - 200, SCREEN_HEIGHT - 230)
       pygame.draw.rect(screen, (240, 240, 240), list_rect)
       pygame.draw.rect(screen, BLACK, list_rect, 2)

       # 디렉토리 항목 표시
       try:
           items = list_directory(current_path)
           visible_items = 15  # 화면에 표시할 항목 수

           # 스크롤 범위 조정
           max_scroll = max(0, len(items) - visible_items)
           scroll_offset = min(max_scroll, scroll_offset)

           for i in range(scroll_offset, min(scroll_offset + visible_items, len(items))):
               item_name, is_dir = items[i]
               y_pos = list_rect.y + (i - scroll_offset) * 30 + 5

               # 선택된 항목 강조
               item_rect = pygame.Rect(list_rect.x + 5, y_pos, list_rect.width - 10, 25)
               if i == selected_index:
                   pygame.draw.rect(screen, (180, 220, 180), item_rect)

               # 아이콘 (디렉토리/파일)
               if is_dir:
                   icon_text = "📁"
               elif item_name.lower().endswith(('.xlsx', '.xls')):
                   icon_text = "📊"  # 엑셀 파일 아이콘
               elif item_name.lower().endswith('.csv'):
                   icon_text = "📋"  # CSV 파일 아이콘
               else:
                   icon_text = "📄"

               icon = small_font.render(icon_text, True, BLACK)
               screen.blit(icon, (list_rect.x + 10, y_pos + 3))

               # 파일/디렉토리 이름
               item_text = small_font.render(item_name, True, BLACK)
               screen.blit(item_text, (list_rect.x + 40, y_pos + 3))

           # 스크롤바 (항목이 많을 경우)
           if len(items) > visible_items:
               scrollbar_height = (list_rect.height * visible_items) / len(items)
               scrollbar_pos = list_rect.y + (list_rect.height * scroll_offset) / len(items)
               scrollbar_rect = pygame.Rect(list_rect.x + list_rect.width - 10, scrollbar_pos, 5, scrollbar_height)
               pygame.draw.rect(screen, (150, 150, 150), scrollbar_rect)

       except Exception as e:
           error_text = small_font.render(f"디렉토리 접근 오류: {str(e)}", True, RED)
           screen.blit(error_text, (list_rect.x + 10, list_rect.y + 10))

       # 안내 텍스트
       guide_text1 = small_font.render("↑/↓: 항목 이동, Enter: 선택, Backspace: 상위 폴더, ESC: 취소", True, BLACK)
       guide_text2 = small_font.render("Excel(.xlsx, .xls) 또는 CSV(.csv) 파일을 선택하세요.", True, BLACK)

       screen.blit(guide_text1, (SCREEN_WIDTH//2 - guide_text1.get_width()//2, list_rect.y + list_rect.height + 20))
       screen.blit(guide_text2, (SCREEN_WIDTH//2 - guide_text2.get_width()//2, list_rect.y + list_rect.height + 45))

       pygame.display.flip()
       clock.tick(30)

def list_directory(path):
   """지정된 경로의 모든 파일과 디렉토리를 목록으로 반환"""
   items = []
   for item in os.listdir(path):
       full_path = os.path.join(path, item)
       is_dir = os.path.isdir(full_path)
       # 숨김 파일 제외 (선택적)
       if not item.startswith('.'):
           items.append((item, is_dir))

   # 디렉토리 먼저, 그 다음 파일 (알파벳 순)
   return sorted(items, key=lambda x: (not x[1], x[0].lower()))

def load_orders_from_file(filename=None):
   """엑셀 또는 CSV 파일에서 주문 및 아이템 정보를 읽어옵니다."""
   try:
       # pandas 라이브러리 임포트
       import pandas as pd
       import numpy as np

       # openpyxl 설치 확인 (Excel 파일용)
       try:
           import openpyxl
       except ImportError:
           logging.warning("openpyxl 패키지가 설치되어 있지 않습니다. Excel 파일을 읽지 못할 수 있습니다.")

       # 항상 파일 선택 대화상자 표시
       logging.info("파일 선택 대화상자를 표시합니다.")
       file_path = select_file_pygame()

       if not file_path:
           logging.warning("파일 선택이 취소되었습니다.")
           return None

       # 파일 확장자 확인
       file_ext = os.path.splitext(file_path)[1].lower()

       # 파일 읽기
       logging.info(f"파일 '{file_path}' 읽는 중...")

       try:
           # 파일 형식에 따라 적절한 방법으로 데이터 읽기
           if file_ext == '.csv':
               orders_data = pd.read_csv(file_path)
               logging.info("CSV 파일을 읽었습니다.")
           elif file_ext in ['.xlsx', '.xls']:
               orders_data = pd.read_excel(file_path, engine='openpyxl')
               logging.info("Excel 파일을 읽었습니다.")
           else:
               logging.error(f"지원하지 않는 파일 형식입니다: {file_ext}")
               show_error_message(f"지원하지 않는 파일 형식입니다: {file_ext}\n엑셀(.xlsx, .xls) 또는 CSV(.csv) 파일만 지원합니다.")
               return None

           # 데이터 구조 정보 출력
           logging.info(f"파일 열 정보: {orders_data.columns.tolist()}")
           logging.info(f"파일 데이터 형태: {orders_data.shape}")

           # 첫 5개 행 정보 출력
           logging.info("파일 데이터 샘플:")
           for i in range(min(5, len(orders_data))):
               logging.info(f"행 {i+1}: {orders_data.iloc[i].to_dict()}")

           # 주문 ID 열 확인 - 대체 가능한 이름들
           order_id_columns = ['Order ID', 'order_id', 'order', 'orderid', 'id', 'order id', '주문번호', '주문 번호']
           found_order_id_col = None

           for col_name in order_id_columns:
               if col_name in orders_data.columns:
                   found_order_id_col = col_name
                   break

           if found_order_id_col:
               # 주문 ID 열 이름 통일
               orders_data = orders_data.rename(columns={found_order_id_col: 'order_id'})
               logging.info(f"주문 ID 열 '{found_order_id_col}'을(를) 'order_id'로 매핑했습니다.")
           else:
               # 주문 ID 열이 없으면 첫 번째 열을 사용
               orders_data = orders_data.copy()
               orders_data['order_id'] = orders_data.iloc[:, 0]
               logging.warning(f"주문 ID 열을 찾을 수 없어 첫 번째 열을 사용합니다.")

           # 아이템 수량 열 확인 - 대체 가능한 이름들
           num_items_columns = ['Number of Items', 'num_items', 'items', 'quantity', '아이템 수', '수량']
           found_num_items_col = None

           for col_name in num_items_columns:
               if col_name in orders_data.columns:
                   found_num_items_col = col_name
                   break

           if found_num_items_col:
               # 아이템 수량 열 이름 통일
               orders_data = orders_data.rename(columns={found_num_items_col: 'num_items'})
               logging.info(f"아이템 수량 열 '{found_num_items_col}'을(를) 'num_items'로 매핑했습니다.")

           # 위치 열 찾기 - 모든 가능한 방법 시도
           location_columns = []

           # 1. "item" + "location" 패턴 (대소문자 무시)
           for col in orders_data.columns:
               col_str = str(col).lower()
               if 'item' in col_str and 'location' in col_str:
                   location_columns.append(col)

           # 2. "location" 포함된 열
           if not location_columns:
               for col in orders_data.columns:
                   col_str = str(col).lower()
                   if 'location' in col_str:
                       location_columns.append(col)

           # 3. "좌표" 형식의 값을 가진 열 확인 (첫 10행 샘플링)
           if not location_columns and len(orders_data) > 0:
               import re
               for col in orders_data.columns:
                   # 이미 찾은 열은 건너뛰기
                   if col == 'order_id' or (found_num_items_col and col == 'num_items'):
                       continue

                   # 처음 10개 행 또는 전체 행 중 작은 수 샘플링
                   sample_size = min(10, len(orders_data))
                   coord_pattern_found = False

                   for i in range(sample_size):
                       if i >= len(orders_data):
                           break

                       # 각 셀의 값 확인
                       cell_val = str(orders_data[col].iloc[i])
                       if pd.isna(orders_data[col].iloc[i]) or cell_val.strip() == '':
                           continue  # 빈 셀 무시

                       # (숫자,숫자) 패턴 확인
                       if re.search(r'\(\s*\d+(\.\d+)?\s*,\s*\d+(\.\d+)?\s*\)', cell_val):
                           coord_pattern_found = True
                           break

                   if coord_pattern_found:
                       location_columns.append(col)
                       logging.info(f"좌표 형식 값을 가진 열 발견: {col}")

           # 모든 시도 후에도 위치 열을 찾지 못한 경우 - 모든 숫자 열을 후보로 고려
           if not location_columns:
               logging.warning("위치 형식의 열을 찾지 못했습니다. 모든 숫자 열을 사용합니다.")
               for col in orders_data.columns:
                   if col != 'order_id' and col != 'num_items':
                       # 첫 행이 숫자 형태인지 확인
                       if len(orders_data) > 0:
                           try:
                               val = orders_data[col].iloc[0]
                               if pd.notna(val) and (isinstance(val, (int, float)) or
                                                   (isinstance(val, str) and any(c.isdigit() for c in val))):
                                   location_columns.append(col)
                           except:
                               pass

           # 오름차순으로 정렬 (Item 1 Location, Item 2 Location, ... 순서로)
           if location_columns:
               # 숫자 기준으로 정렬 시도
               try:
                   import re
                   # 열 이름에서 숫자 추출
                   def extract_number(col_name):
                       match = re.search(r'(\d+)', str(col_name))
                       if match:
                           return int(match.group(1))
                       return float('inf')  # 숫자가 없으면 가장 뒤로

                   location_columns.sort(key=extract_number)
               except:
                   # 정렬 실패시 원래 순서 유지
                   pass

           if location_columns:
               logging.info(f"위치 정보 열 {len(location_columns)}개를 발견했습니다: {location_columns}")
               # 위치 열 정보 저장
               orders_data.attrs['location_columns'] = location_columns

               # 기타 정보 저장
               if found_num_items_col:
                   orders_data.attrs['has_num_items'] = True
               else:
                   orders_data.attrs['has_num_items'] = False

               return orders_data
           else:
               logging.error("위치 정보 열을 찾을 수 없습니다.")
               show_error_message("파일에 아이템 위치 정보 열(Item X Location)이 없습니다.")
               return None

       except Exception as file_error:
           logging.error(f"파일 읽기 오류: {file_error}")
           show_error_message(f"파일을 읽는 중 오류가 발생했습니다:\n{str(file_error)}")
           return None

   except Exception as e:
       logging.error(f"파일 로드 오류: {e}")
       show_error_message(f"파일 로드 중 오류가 발생했습니다:\n{str(e)}")
       return None

def show_error_message(message):
   """오류 메시지를 화면에 표시"""
   waiting = True
   while waiting:
       for event in pygame.event.get():
           if event.type == pygame.QUIT:
               pygame.quit(); sys.exit()
           if event.type == pygame.KEYDOWN or event.type == pygame.MOUSEBUTTONDOWN:
               waiting = False

       screen.fill(WHITE)
       title_text = status_font.render("오류 발생", True, RED)
       screen.blit(title_text, (SCREEN_WIDTH//2 - title_text.get_width()//2, SCREEN_HEIGHT//2 - 100))

       # 오류 메시지 표시 (여러 줄로 나눌 수 있음)
       lines = [message[i:i+60] for i in range(0, len(message), 60)]
       for i, line in enumerate(lines):
           msg_text = sim_font.render(line, True, BLACK)
           screen.blit(msg_text, (SCREEN_WIDTH//2 - msg_text.get_width()//2, SCREEN_HEIGHT//2 - 50 + i*25))

       continue_text = sim_font.render("계속하려면 아무 키나 누르세요", True, BLACK)
       screen.blit(continue_text, (SCREEN_WIDTH//2 - continue_text.get_width()//2, SCREEN_HEIGHT//2 + 100))

       pygame.display.flip()
       clock.tick(30)

import os
def create_sample_excel():
   """샘플 엑셀 파일 생성"""
   try:
       import pandas as pd
       import numpy as np

       # 샘플 데이터 생성
       num_orders = 50
       orders_data = []

       for order_id in range(1, num_orders + 1):
           num_items = np.random.randint(1, 10)  # 각 주문당 1-10개 아이템

           for _ in range(num_items):
               # 창고 크기에 맞는 랜덤 위치 생성
               row = np.random.randint(0, WAREHOUSE_ROWS)
               column = np.random.randint(0, WAREHOUSE_COLS)

               # 주문 데이터 추가
               orders_data.append({
                   'order_id': order_id,
                   'row': row,
                   'column': column,
                   'quantity': 1
               })

       # DataFrame 생성
       df = pd.DataFrame(orders_data)

       # 엑셀 파일로 저장
       filename = "sample_orders.xlsx"
       df.to_excel(filename, index=False)

       logging.info(f"샘플 엑셀 파일이 생성되었습니다: {filename}")
       return filename

   except Exception as e:
       logging.error(f"샘플 엑셀 파일 생성 오류: {e}")
       return None
import re

def generate_items_from_excel_data(orders_data):
   """
   엑셀 데이터를 읽어
     1) 주문 객체 생성
     2) Item N Location 열들을 melt → long 포맷
     3) (row,col,z) 파싱 → 0-based (x=col-1, y=row-1)
     4) shelf_positions에 없으면 최근접으로 클리핑
     5) shelf_inventory/backorder 초기화
   """
   global shelf_inventory, shelf_backorder, shelf_positions

   # 1) 주문 객체 초기화
   orders_data = orders_data.rename(columns={
       'Order ID': 'order_id',
       'Number of Items': 'num_items'
   })
   orders = {}
   for _, row in orders_data.iterrows():
       oid = int(row['order_id'])
       orders[oid] = Order(oid, int(row['num_items']))

   # 2) “Item N Location” 열 감지
   location_cols = [c for c in orders_data.columns if re.match(r'Item \d+ Location', c)]

   # 3) melt → long 포맷
   melted = orders_data.melt(
       id_vars=['order_id'],
       value_vars=location_cols,
       var_name='item_idx',
       value_name='location'
   ).dropna(subset=['location'])

   # 4) 선반 재고 초기화
   shelf_inventory = {}
   shelf_backorder = {}
   for pos in shelf_positions:
       shelf_inventory[pos] = 500
       shelf_backorder[pos] = 0

   items = []
   # 5) 좌표 파싱 및 Item 생성
   coords = melted['location'].astype(str).str.extract(
       r'\(\s*(?P<row>\d+)\s*,\s*(?P<col>\d+)\s*,\s*(?P<z>\d+)\s*\)'
   ).astype(int)

   for idx, m in melted.iterrows():
       oid = int(m['order_id'])
       excel_row = coords.at[idx, 'row']
       excel_col = coords.at[idx, 'col']

       # 1-based → 0-based
       sim_x = excel_col - 1
       sim_y = excel_row - 1

       # 범위 클리핑
       sim_x = max(0, min(sim_x, WAREHOUSE_COLS - 1))
       sim_y = max(0, min(sim_y, WAREHOUSE_ROWS - 1))

       # 선반 외 위치는 가장 가까운 선반으로
       if (sim_x, sim_y) not in shelf_positions:
           sim_x, sim_y = min(
               shelf_positions,
               key=lambda p: abs(p[0] - sim_x) + abs(p[1] - sim_y)
           )

       # 객체 생성
       it = Item(sim_x, sim_y, oid)
       it.number = 1
       orders[oid].add_item(it)
       items.append(it)

   return list(orders.values()), items

def get_data_source():
   """데이터 소스를 선택하는 화면 표시"""
   button_width, button_height = 300, 100
   random_button = pygame.Rect(SCREEN_WIDTH//2 - button_width - 20, SCREEN_HEIGHT//2 - button_height//2, button_width, button_height)
   excel_button = pygame.Rect(SCREEN_WIDTH//2 + 20, SCREEN_HEIGHT//2 - button_height//2, button_width, button_height)

   while True:
       for event in pygame.event.get():
           if event.type == pygame.QUIT:
               pygame.quit(); sys.exit()
           elif event.type == pygame.MOUSEBUTTONDOWN:
               pos = pygame.mouse.get_pos()
               if random_button.collidepoint(pos):
                   return "RANDOM"
               elif excel_button.collidepoint(pos):
                   return "EXCEL"

       screen.fill(WHITE)
       title_surf = title_font.render("데이터 소스 선택", True, BLACK)
       screen.blit(title_surf, (SCREEN_WIDTH//2 - title_surf.get_width()//2, SCREEN_HEIGHT//2 - 150))

       # 랜덤 생성 버튼
       pygame.draw.rect(screen, (200, 230, 200), random_button)
       pygame.draw.rect(screen, BLACK, random_button, 2)
       random_text = input_font.render("랜덤 생성", True, BLACK)
       screen.blit(random_text, (random_button.x + random_button.width//2 - random_text.get_width()//2,
                                 random_button.y + random_button.height//2 - random_text.get_height()//2))
       random_desc = sim_font.render("주문과 아이템 위치를 랜덤으로 생성", True, BLACK)
       screen.blit(random_desc, (random_button.x + random_button.width//2 - random_desc.get_width()//2,
                                 random_button.y + random_button.height//2 + 20))

       # 엑셀 파일 버튼
       pygame.draw.rect(screen, (230, 200, 200), excel_button)
       pygame.draw.rect(screen, BLACK, excel_button, 2)
       excel_text = input_font.render("엑셀 파일", True, BLACK)
       screen.blit(excel_text, (excel_button.x + excel_button.width//2 - excel_text.get_width()//2,
                               excel_button.y + excel_button.height//2 - excel_text.get_height()//2))
       excel_desc = sim_font.render("엑셀 파일에서 주문 정보 불러오기", True, BLACK)
       screen.blit(excel_desc, (excel_button.x + excel_button.width//2 - excel_desc.get_width()//2,
                               excel_button.y + excel_button.height//2 + 20))

       pygame.display.flip()
       clock.tick(30)

def get_agv_count_input():
   """AGV 대수만 입력받는 화면"""
   box_w, box_h = 250, 50
   input_box = pygame.Rect(SCREEN_WIDTH//2 - box_w//2, SCREEN_HEIGHT//2, box_w, box_h)
   input_text = ""

   while True:
       for event in pygame.event.get():
           if event.type == pygame.QUIT:
               pygame.quit(); sys.exit()
           elif event.type == pygame.KEYDOWN:
               if event.key == pygame.K_RETURN:
                   try:
                       agv_count = int(input_text)
                       agv_count = max(0, min(60, agv_count))
                       return agv_count
                   except:
                       input_text = ""
               elif event.key == pygame.K_BACKSPACE:
                   input_text = input_text[:-1]
               else:
                   if event.unicode.isdigit():
                       input_text += event.unicode

       screen.fill(WHITE)
       title_surf = title_font.render("AGV 대수 입력", True, BLACK)
       screen.blit(title_surf, (SCREEN_WIDTH//2 - title_surf.get_width()//2, SCREEN_HEIGHT//2 - 100))

       pygame.draw.rect(screen, (230,230,230), input_box)
       pygame.draw.rect(screen, BLACK, input_box, 2)

       prompt_surf = input_font.render("AGV 대수 (0-60):", True, BLACK)
       screen.blit(prompt_surf, (input_box.x - prompt_surf.get_width() - 10,
                               input_box.y + (input_box.height - prompt_surf.get_height()) // 2))

       in_surf = input_font.render(input_text, True, BLACK)
       screen.blit(in_surf, (input_box.x+5, input_box.y + (input_box.height - in_surf.get_height()) // 2))

       guide_surf = input_font.render("값을 입력 후 Enter 키를 누르세요", True, BLACK)
       screen.blit(guide_surf, (SCREEN_WIDTH//2 - guide_surf.get_width()//2, SCREEN_HEIGHT//2 + 80))

       pygame.display.flip()
       clock.tick(30)
    
# ── Human 대수 입력 함수 추가 ─────────────────────────────────
def get_human_count_input():
    """Human 대수만 입력받는 화면"""
    box_w, box_h = 250, 50
    input_box = pygame.Rect(SCREEN_WIDTH//2 - box_w//2, SCREEN_HEIGHT//2, box_w, box_h)
    input_text = ""

    while True:
        for event in pygame.event.get():
            if event.type == pygame.QUIT:
                pygame.quit(); sys.exit()
            elif event.type == pygame.KEYDOWN:
                if event.key == pygame.K_RETURN:
                    try:
                        human_count = int(input_text)
                        human_count = max(0, min(60, human_count))
                        return human_count
                    except:
                        input_text = ""
                elif event.key == pygame.K_BACKSPACE:
                    input_text = input_text[:-1]
                else:
                    if event.unicode.isdigit():
                        input_text += event.unicode

        screen.fill(WHITE)
        title_surf = title_font.render("Human 수 입력", True, BLACK)
        screen.blit(title_surf, (SCREEN_WIDTH//2 - title_surf.get_width()//2, SCREEN_HEIGHT//2 - 100))

        pygame.draw.rect(screen, (230,230,230), input_box)
        pygame.draw.rect(screen, BLACK, input_box, 2)

        prompt_surf = input_font.render("Human 수 (0-60):", True, BLACK)
        screen.blit(prompt_surf, (
            input_box.x - prompt_surf.get_width() - 10,
            input_box.y + (input_box.height - prompt_surf.get_height()) // 2
        ))

        in_surf = input_font.render(input_text, True, BLACK)
        screen.blit(in_surf, (
            input_box.x + 5,
            input_box.y + (input_box.height - in_surf.get_height()) // 2
        ))

        guide_surf = input_font.render("값을 입력 후 Enter 키를 누르세요", True, BLACK)
        screen.blit(guide_surf, (
            SCREEN_WIDTH//2 - guide_surf.get_width()//2,
            SCREEN_HEIGHT//2 + 80
        ))

        pygame.display.flip()
        clock.tick(30)
# ────────────────────────────────────────────────────────────────

def main():
   global simulation_speed, region_scroll_offset, agvs, humans
   global time_points, completed_orders_points, completed_items_points
   global items, total_orders, items_per_order, total_agvs, total_humans
   global grid_map, reserved_positions, shelf_inventory, shelf_backorder
   global heatmap_data
   global dropoff_positions

   humans = []
   sim_time = 0
   # 그래프 데이터 초기화
   time_points = []
   completed_orders_points = []
   completed_items_points = []

   region_scroll_offset = 0

   # ── 배경 캐싱 시작 ────────────────────────────
   screen.fill(WHITE)
   draw_grid()
   draw_zones()
   draw_shelves()
   background = screen.copy()
   logging.info("배경 캐싱 완료")
   # ────────────────────────────────────────────────

   while True:  # 메인 루프
       logging.info("시뮬레이션 시작")
       screen.blit(background, (0, 0)) 
       grid_map = [[0 for _ in range(GRID_COLS)] for _ in range(GRID_ROWS)]
       reserved_positions = set()
       shelf_inventory = {}
       shelf_backorder = {}
       dropoff_positions = []

       # 히트맵 초기화
       initialize_heatmap()

       screen.blit(background, (0, 0))  # 캐시된 배경을 빠르게 복사

       # 출구 위치를 dropoff_positions에 추가
       dropoff_positions = exit_positions.copy()
       
       pygame.display.flip()

       # 데이터 소스 선택
       data_source = get_data_source()

       if data_source == "RANDOM":
           # 기존 방식 - 랜덤 생성
           # ① 사용자 입력에서 Human 대수까지 받아오기
           inp_orders, inp_items, inp_agvs, inp_humans, random_items = get_simulation_input()
           total_orders, items_per_order, total_agvs, total_humans = inp_orders, inp_items, inp_agvs, inp_humans

           screen.fill(WHITE)
           draw_grid(); draw_zones(); draw_shelves()
           pygame.display.flip()

           # ── AGV+Human 영역 설정 ─────────────────────────────
           regions, speeds = setup_agv_regions(total_agvs, total_humans)
           pygame.event.clear()

           agv_regions   = regions[:total_agvs]
           human_regions = regions[total_agvs:]

           agv_speeds    = speeds[:total_agvs]
           human_speeds  = speeds[total_agvs:]
           # ────────────────────────────────────────────────────────────

           # ── AGV/Human 라벨 위치: 영역 중앙 상단으로 재계산 ─────────────────
           agv_label_positions = []
           for reg in agv_regions:
               if reg:
                   xs = [x for x, y in reg]
                   ys = [y for x, y in reg]
                   min_y = min(ys)
                   avg_x = sum(xs) / len(xs)
                   agv_label_positions.append([(int(avg_x), min_y)])
               else:
                   agv_label_positions.append([])
            
           # → Human 영역 레이블 위치도 동일하게 계산
           human_label_positions = []
           for reg in human_regions:
               if reg:
                    xs = [x for x, y in reg]
                    ys = [y for x, y in reg]
                    min_y = min(ys)
                    avg_x = sum(xs) / len(xs)
                    human_label_positions.append([(int(avg_x), min_y)])
               else:
                    human_label_positions.append([])

           orders = []
           for i in range(total_orders):
               num_items = items_per_order
               od = Order(i+1, num_items)
               if total_agvs > 0:
                   od.agv_region = i % total_agvs
               else:
                   od.agv_region = 0  # AGV가 없을 때는 기본값 0 사용
               orders.append(od)

           logging.info("아이템 생성 시작...")
           # AGV+Human 영역 기준으로 아이템 생성
           items = generate_items(orders, agv_regions, human_regions)
           logging.info(f"생성된 아이템 수: {len(items)}")

           # ── AGV 생성 및 구역 할당
           logging.info(f"AGV {total_agvs}대 생성 중.")
           agvs = create_agvs(total_agvs)
           for idx, a in enumerate(agvs):
               a.assigned_region = agv_regions[idx]
           logging.info("AGV 구역 할당 완료")

           # ── Human 생성 및 구역 할당
           logging.info(f"Human {total_humans}대 생성 중.")
           humans = []
           for i in range(total_humans):
               # 파란색 대기 구역이 충분하면 거기서, 아니면 지정된 영역 첫 좌표에서 생성
               if waiting_positions and i < len(waiting_positions):
                   sx, sy = waiting_positions[i]
                   logging.info(f"Human-{i+1}을 파란색 대기 구역 ({sx}, {sy})에 생성합니다.")
               else:
                   if human_regions[i]:
                       sx, sy = human_regions[i][0]
                       logging.info(f"Human-{i+1}을 지정 영역 ({sx}, {sy})에 생성합니다.")
                   else:
                       sx, sy = 0, 0
                       logging.info(f"Human-{i+1}을 기본 위치 (0, 0)에 생성합니다.")
               h = Human(i+1, sx, sy, human_speeds[i])
               h.assigned_region = human_regions[i]
               humans.append(h)
           logging.info(f"Human {len(humans)}대 생성 완료")

           # ── 아이템을 AGV/Human에 할당
           logging.info("아이템을 에이전트에 할당 중...")
           item_assigned_count = 0
           agv_region_items   = [[] for _ in range(len(agv_regions))]
           human_region_items = [[] for _ in range(len(human_regions))]
           unassigned_items   = []

           for it in items:
               assigned = False
               # ① Human 구역 우선 분류
               for idx, reg in enumerate(human_regions):
                   if (it.x, it.y) in reg:
                       human_region_items[idx].append(it)
                       assigned = True
                       break
               # ② AGV 구역 분류
               if not assigned:
                   for idx, reg in enumerate(agv_regions):
                       if (it.x, it.y) in reg:
                           agv_region_items[idx].append(it)
                           assigned = True
                           break
               # ③ 어느 구역에도 없으면 미할당
               if not assigned:
                   unassigned_items.append(it)

           # ④ AGV 아이템 할당 - 무거운 순(내림차순)
           for idx, region_items in enumerate(agv_region_items):
               region_items.sort(key=lambda i: i.number, reverse=True)
               for it in region_items:
                   agvs[idx].assigned_items.append(it)
                   it.assigned_agv_id = agvs[idx].id
                   item_assigned_count += 1

           # ⑤ Human 아이템 할당 - 가벼운 순(오름차순)
           for idx, region_items in enumerate(human_region_items):
               region_items.sort(key=lambda i: i.number)
               for it in region_items:
                   humans[idx].assigned_items.append(it)
                   it.assigned_human_id = humans[idx].id
                   item_assigned_count += 1

           # ⑥ 미할당 아이템 할당 – AGV/Human 개수별 안전 처리
           # 방어 코드: 에이전트가 단 1개도 없으면 시뮬레이션 중단
           if not agvs and not humans:
               logging.error("에이전트를 하나도 선택하지 않아 시뮬레이션을 진행할 수 없습니다.")
               show_error_message("AGV 또는 Human 대수를 1 이상으로 설정해주세요.")
               return
           # (0) 둘 중 하나만 있으면 그쪽에 전부 할당 후 로직 종료
           if len(agvs) == 0 and len(humans) > 0:
               for i, it in enumerate(unassigned_items):
                   h = humans[i % len(humans)]
                   h.assigned_items.append(it)
                   it.assigned_human_id = h.id
                   item_assigned_count += 1
               logging.info("AGV가 0이므로 모든 미할당 아이템을 Human에 할당합니다.")
               goto_end_of_assignment = True
           elif len(humans) == 0 and len(agvs) > 0:
               for i, it in enumerate(unassigned_items):
                   a = agvs[i % len(agvs)]
                   a.assigned_items.append(it)
                   it.assigned_agv_id = a.id
                   item_assigned_count += 1
               logging.info("Human이 0이므로 모든 미할당 아이템을 AGV에 할당합니다.")
               goto_end_of_assignment = True
           else:
               goto_end_of_assignment = False

           # ── (1) skip되지 않았다면 안전 할당 로직으로 대체 ───────────────────────────
           if not goto_end_of_assignment:
               # AGV/Human 중 영역 지정 여부 판정
               agv_has_region   = any(len(reg) > 0 for reg in agv_regions)
               human_has_region = any(len(reg) > 0 for reg in human_regions)

               if not agv_has_region and not human_has_region:
                   # (1) 전체 비지정 시: AGV/Human 개수별 안전 할당
                   if len(agvs) == 0 and len(humans) > 0:
                       for i, it in enumerate(unassigned_items):
                           h = humans[i % len(humans)]
                           h.assigned_items.append(it)
                           it.assigned_human_id = h.id
                           item_assigned_count += 1
                   elif len(humans) == 0 and len(agvs) > 0:
                       for i, it in enumerate(unassigned_items):
                           a = agvs[i % len(agvs)]
                           a.assigned_items.append(it)
                           it.assigned_agv_id = a.id
                           item_assigned_count += 1
                   else:
                       # 양쪽 모두 있을 때만 절반씩
                       mid = len(unassigned_items) // 2
                       for i, it in enumerate(unassigned_items[:mid]):
                           agent = agvs[i % len(agvs)]
                           agent.assigned_items.append(it)
                           it.assigned_agv_id = agent.id
                           item_assigned_count += 1
                       for i, it in enumerate(unassigned_items[mid:]):
                           agent = humans[i % len(humans)]
                           agent.assigned_items.append(it)
                           it.assigned_human_id = agent.id
                           item_assigned_count += 1

               else:
                   # (2) 일부만 지정된 경우: 미지정 에이전트가 전체 창고 아이템을 지원
                   unassigned_agents = [
                       agvs[i]   for i, r in enumerate(agv_regions)   if not r
                   ] + [
                       humans[i] for i, r in enumerate(human_regions) if not r
                   ]
                   if unassigned_agents:
                       support_items = [
                           it for it in items
                           if not it.picked
                           and it.assigned_agv_id   is None
                           and getattr(it, 'assigned_human_id', None) is None
                       ]
                       for idx, it in enumerate(support_items):
                           agent = unassigned_agents[idx % len(unassigned_agents)]
                           agent.assigned_items.append(it)
                           if isinstance(agent, AGV):
                               it.assigned_agv_id   = agent.id
                           else:
                               it.assigned_human_id = agent.id
                           item_assigned_count += 1

               logging.info(f"{item_assigned_count}개 아이템 할당 완료")
           # ───────────────────────────────────────────

           # ⑥ 초기 경로 계산 (AGV & Human)
           for a in agvs:
               success = a.find_next_item()
               a.path_history = [(a.x, a.y)]
           for h in humans:
               success = h.find_next_item()
               h.path_history = [(h.x, h.y)]
           logging.info("에이전트 초기 경로 계산 완료")

# main() 함수 내 EXCEL 처리 부분
       else:  # EXCEL
           try:
               # 파일에서 데이터 로드 (이름을 load_orders_from_file로 변경)
               orders_data = load_orders_from_file()
               if orders_data is None:
                   logging.error("파일 로드 실패, 메인 메뉴로 돌아갑니다.")
                   continue  # 메인 루프로 돌아가기

               # AGV 대수 입력 받기
               screen.fill(WHITE)
               inp_agvs = get_agv_count_input()
               total_agvs = inp_agvs

               # ── Human 대수 입력 받기 ─────────────────  
               screen.fill(WHITE)  
               inp_humans = get_human_count_input()  
               total_humans = inp_humans  
               # ── 방어 코드: AGV와 Human이 모두 0이면 재입력 유도 ─────────────────
               if total_agvs == 0 and total_humans == 0:
                    logging.error("AGV와 Human을 모두 0으로 설정할 수 없습니다.")
                    show_error_message("AGV와 Human 중 최소 하나는 1 이상이어야 합니다. 다시 입력해주세요.")
                    continue
               # ────────────────────────────────────────  

               screen.fill(WHITE)
               draw_grid(); draw_zones(); draw_shelves()
               pygame.display.flip()

               # ── AGV+Human 영역 설정 ─────────────────────────────
               regions, speeds = setup_agv_regions(total_agvs, total_humans)
               pygame.event.clear()  # 잔여 이벤트 제거

               agv_regions   = regions[:total_agvs]
               human_regions = regions[total_agvs:]

               agv_speeds    = speeds[:total_agvs]
               human_speeds = speeds[total_agvs:]
               # ────────────────────────────────────────────────────────────

               # AGV ID를 표시할 고정된 위치 미리 결정
               agv_label_positions = []
               for reg in agv_regions:
                   if reg:
                       xs = [x for x,y in reg]
                       ys = [y for x,y in reg]
                       min_y  = min(ys)
                       avg_x  = int(sum(xs) / len(xs))
                       # 최상단(min_y), 중앙(avg_x) 한 점만 선택
                       agv_label_positions.append([(avg_x, min_y)])
                   else:
                       agv_label_positions.append([])
               
               # → Human 영역 레이블 위치도 동일하게 계산
               human_label_positions = []
               for reg in human_regions:
                    if reg:
                        xs = [x for x, y in reg]
                        ys = [y for x, y in reg]
                        min_y = min(ys)
                        avg_x = sum(xs) / len(xs)
                        human_label_positions.append([(int(avg_x), min_y)])
                    else:
                        human_label_positions.append([])
               # 엑셀 데이터로 주문 및 아이템 생성
               logging.info("엑셀 데이터에서 주문 및 아이템 생성 중...")
               orders, items = generate_items_from_excel_data(orders_data)

               # 생성 실패 체크
               if orders is None or items is None or len(orders) == 0 or len(items) == 0:
                   logging.error("주문 및 아이템 생성 실패, 메인 메뉴로 돌아갑니다.")
                   # 사용자에게 오류 표시
                   show_error_message("엑셀 데이터에서 주문 및 아이템을 생성할 수 없습니다.\n데이터 형식을 확인하세요.")
                   continue  # 메인 루프로 돌아가기

               logging.info(f"총 {len(orders)}개 주문, {len(items)}개 아이템 생성 완료")

           except Exception as e:
               logging.error(f"엑셀 데이터 처리 중 오류: {e}")
               show_error_message(f"엑셀 데이터 처리 중 오류가 발생했습니다: {str(e)}")
               continue  # 메인 루프로 돌아가기

       # AGV 생성 및 설정
       logging.info(f"AGV {total_agvs}대 생성 중...")
       agvs = []
       for i in range(total_agvs):
           if charger_positions:
               sx, sy = charger_positions[i % len(charger_positions)]
               a = AGV(i+1, sx, sy, agv_speeds[i])
               a.region_index = i
               agvs.append(a)
       logging.info(f"AGV {len(agvs)}대 생성 완료")

       for i, a in enumerate(agvs):
           a.assigned_region = agv_regions[i]
       logging.info("AGV 구역 할당 완료")

       # Human 생성 및 설정 (공통 부분)
       logging.info(f"Human {total_humans}대 생성 중...")
       humans = []  # 이전에 생성된 humans를 리셋
       for i in range(total_humans):
           # 파란색 구역(waiting_positions)에서 생성
           if waiting_positions and i < len(waiting_positions):
               sx, sy = waiting_positions[i]
               logging.info(f"Human-{i+1}을 파란색 대기 구역 ({sx}, {sy})에 생성합니다.")
           else:
               # 대기 구역이 부족한 경우 대체 위치 사용
               if human_regions[i]:
                   sx, sy = human_regions[i][0]
                   logging.info(f"Human-{i+1}을 지정 영역 ({sx}, {sy})에 생성합니다.")
               else:
                   sx, sy = 0, 0
                   logging.info(f"Human-{i+1}을 기본 위치 (0, 0)에 생성합니다.")
           
           h = Human(i+1, sx, sy, human_speeds[i])
           h.assigned_region = human_regions[i]
           humans.append(h)
       logging.info(f"Human {len(humans)}대 생성 완료")

       # 아이템 할당
       logging.info("아이템을 에이전트에 할당 중...")
       item_assigned_count = 0

       # 1. 영역 별로 아이템을 분류합니다
       agv_region_items = [[] for _ in range(len(agv_regions))]
       human_region_items = [[] for _ in range(len(human_regions))]
       unassigned_items = []

       for it in items:
           assigned = False
           
           # Human 영역 확인을 먼저 수행 (우선순위 부여)
           for idx, reg in enumerate(human_regions):
               if (it.x, it.y) in reg:
                   human_region_items[idx].append(it)
                   assigned = True
                   break
           
           # Human 영역에 없는 경우만 AGV 영역 확인
           if not assigned:
               for idx, reg in enumerate(agv_regions):
                   if (it.x, it.y) in reg:
                       agv_region_items[idx].append(it)
                       assigned = True
                       break
           
           # 어떤 영역에도 속하지 않는 아이템
           if not assigned:
               unassigned_items.append(it)

       # 2. 각 영역별 아이템을 해당 에이전트에 할당합니다
       # AGV 아이템 할당 - 무거운 순으로 정렬
       for idx, items_in_region in enumerate(agv_region_items):
           if idx < len(agvs) and items_in_region:
               # 무거운 순서로 정렬 (이 부분 추가)
               items_in_region.sort(key=lambda it: it.number, reverse=True)
               for it in items_in_region:
                   agvs[idx].assigned_items.append(it)
                   it.assigned_agv_id = agvs[idx].id
                   item_assigned_count += 1

       # Human 아이템 할당 - 가벼운 순으로 정렬
       for idx, items_in_region in enumerate(human_region_items):
           if idx < len(humans) and items_in_region:
               # 가벼운 순서로 정렬 (이 부분 추가)
               items_in_region.sort(key=lambda it: it.number)
               for it in items_in_region:
                   humans[idx].assigned_items.append(it)
                   it.assigned_human_id = humans[idx].id
                   item_assigned_count += 1

       # 3. 영역 할당되지 않은 아이템 처리
       logging.info(f"영역에 속하지 않는 아이템 {len(unassigned_items)}개 발견")
       
       # 변수 기본값 설정
       goto_end_of_assignment = False

       # ───────────────────────────────────────────────────────
       # (0) AGV/Human 중 하나가 0인 경우: 다른 쪽에 모두 할당
       if len(agvs) == 0 and len(humans) > 0:
           # AGV가 없으면 unassigned_items 전부를 Human에게 할당
           for i, it in enumerate(unassigned_items):
               agent = humans[i % len(humans)]
               agent.assigned_items.append(it)
               it.assigned_human_id = agent.id
               item_assigned_count += 1
           logging.info("AGV가 0이므로 모든 미할당 아이템을 Human에 할당합니다.")
           # 할당 후 아래 로직 건너뛰기
           logging.info(f"{item_assigned_count}개 아이템 할당 완료")
           goto_end_of_assignment = True

       elif len(humans) == 0 and len(agvs) > 0:
           # Human이 없으면 unassigned_items 전부를 AGV에게 할당
           for i, it in enumerate(unassigned_items):
               agent = agvs[i % len(agvs)]
               agent.assigned_items.append(it)
               it.assigned_agv_id = agent.id
               item_assigned_count += 1
           logging.info("Human이 0이므로 모든 미할당 아이템을 AGV에 할당합니다.")
           goto_end_of_assignment = True

       else:
           goto_end_of_assignment = False
       # ───────────────────────────────────────────────────────
           # (1) skip되지 않았다면 기존 로직 수행
           if not goto_end_of_assignment:
               # AGV/Human 중 영역 지정 여부 판정
               agv_has_region   = any(len(reg) > 0 for reg in agv_regions)
               human_has_region = any(len(reg) > 0 for reg in human_regions)

               if not agv_has_region and not human_has_region:
                   # 전체 비지정 시: AGV/Human 개수별 안전 할당
                   if len(agvs) == 0 and len(humans) > 0:
                       for i, it in enumerate(unassigned_items):
                           h = humans[i % len(humans)]
                           h.assigned_items.append(it)
                           it.assigned_human_id = h.id
                           item_assigned_count += 1
                   elif len(humans) == 0 and len(agvs) > 0:
                       for i, it in enumerate(unassigned_items):
                           a = agvs[i % len(agvs)]
                           a.assigned_items.append(it)
                           it.assigned_agv_id = a.id
                           item_assigned_count += 1
                   else:
                       # 양쪽 모두 있을 때만 절반씩
                       mid = len(unassigned_items) // 2
                       for i, it in enumerate(unassigned_items[:mid]):
                           agent = agvs[i % len(agvs)]
                           agent.assigned_items.append(it)
                           it.assigned_agv_id = agent.id
                           item_assigned_count += 1
                       for i, it in enumerate(unassigned_items[mid:]):
                           agent = humans[i % len(humans)]
                           agent.assigned_items.append(it)
                           it.assigned_human_id = agent.id
                           item_assigned_count += 1

               else:
                   # 일부만 지정된 경우: 미지정 에이전트가 전체 창고 아이템을 지원
                   unassigned_agents = [
                       agvs[i]   for i, r in enumerate(agv_regions)   if not r
                   ] + [
                       humans[i] for i, r in enumerate(human_regions) if not r
                   ]
                   if unassigned_agents:
                       support_items = [
                           it for it in items
                           if not it.picked
                           and it.assigned_agv_id   is None
                           and getattr(it, 'assigned_human_id', None) is None
                       ]
                       for idx, it in enumerate(support_items):
                           agent = unassigned_agents[idx % len(unassigned_agents)]
                           agent.assigned_items.append(it)
                           if isinstance(agent, AGV):
                               it.assigned_agv_id   = agent.id
                           else:
                               it.assigned_human_id = agent.id
                           item_assigned_count += 1

               logging.info(f"{item_assigned_count}개 아이템 할당 완료")

       # ⑥ 초기 경로 계산 (AGV & Human)
       logging.info("에이전트 초기 경로 계산 중...")
       for a in agvs:
           success = a.find_next_item()
           a.path_history = [(a.x, a.y)]
           logging.info(f"AGV-{a.id} 초기 경로 계산 결과: {success}, 상태: {a.state}")
       for h in humans:
           success = h.find_next_item()
           h.path_history = [(h.x, h.y)]
           logging.info(f"Human-{h.id} 초기 경로 계산 결과: {success}, 상태: {h.state}")
       logging.info("에이전트 초기 경로 계산 완료")
   
       # 주문 할당
       logging.info("주문을 AGV에 할당 중...")
       agv_orders = [[] for _ in range(total_agvs)]
       for od in orders:
           # 주문이 속한 AGV 영역 결정
           # 간단하게: 주문의 첫 번째 아이템이 속한 AGV 영역으로 할당
           if od.items:
               first_item = od.items[0]
               if hasattr(first_item, 'assigned_agv_id') and first_item.assigned_agv_id is not None:
                   od.agv_region = first_item.assigned_agv_id - 1
               else:
                   od.agv_region = 0
           else:
               od.agv_region = 0

           aid = od.agv_region
           if 0 <= aid < len(agv_orders):
               agv_orders[aid].append(od)

       for i, a in enumerate(agvs):
           if i < len(agv_orders):
               a.assign_orders(agv_orders[i])
       
       # 아이템 검증 코드 추가
       if len(items) == 0:
           logging.error("생성된 아이템이 없습니다. 시뮬레이션을 시작할 수 없습니다.")
           show_error_message("생성된 아이템이 없어 시뮬레이션을 진행할 수 없습니다.\n다시 시도해주세요.")
           continue  # 메인 루프 처음으로 돌아가기

       logging.info("시뮬레이션 모드 선택 화면 표시 직전")
       pygame.event.clear()
       pygame.display.flip()
       clock.tick(15)
       logging.info("시뮬레이션 모드 선택 함수 호출 중...")
       sim_mode = get_simulation_mode()
       logging.info(f"선택된 시뮬레이션 모드: {sim_mode}")

       if sim_mode == "FAST":
           # 고속 시뮬레이션 실행
           show_splash(screen, clock, "고속 시뮬레이션 중… 잠시만 기다려 주세요")
           logging.info("고속 시뮬레이션 시작...")
           try:
               results = run_simulation_fast(agvs, humans, orders, items)
               sim_time = results['sim_time']

               # 결과 데이터 글로벌 변수에 설정
               time_points = results['time_points']
               completed_orders_points = results['completed_orders_points']
               completed_items_points = results['completed_items_points']

               # 최종 시각적 결과 표시
               show_visual_result(agvs, humans, orders, items, sim_time)

               # 최종 통계 화면으로 이동
               final_screen(agvs, orders, sim_time)
           except Exception as e:
               logging.error(f"고속 시뮬레이션 중 오류: {e}")
               show_error_message(f"시뮬레이션 실행 중 오류가 발생했습니다: {str(e)}")
               continue  # 메인 루프로 돌아가기

           # 종료 여부 확인 추가
           should_continue = ask_continue_or_exit()
           if not should_continue:
               logging.info("프로그램 종료합니다.")
               pygame.quit()
               sys.exit()
       else:
           # 기존 시각적 시뮬레이션 실행
           logging.info("시각적 시뮬레이션 시작...")
           sim_time = 0
           sim_running = True
           last_data_record = 0
            # ── 그래프 데이터 초기화 ────────────────────────
           time_points.clear()
           completed_orders_points.clear()
           completed_items_points.clear()

           # 시간 제한 변수 추가
           max_simulation_time = float('inf')  # 시뮬레이션 시간 제한 무한대로 설정
           start_real_time = time.time()  # 실제 시작 시간 기록
           max_real_time = float('inf')  # 실제 실행 시간 제한도 무한대로 설정

           try:
               while sim_running:
                   base_dt = clock.tick(30) / 1000.0
                   dt      = base_dt * simulation_speed
                   sim_time += dt

                   # 시간 제한 검사 추가
                   # 너무 오래 실행되는 것 방지
                   if sim_time > max_simulation_time:
                       logging.warning(f"시뮬레이션 최대 시간({max_simulation_time}초)이 초과되어 종료합니다.")
                       sim_running = False
                       break

                   # 실제 시간 10분 이상 경과 시 강제 종료 (무한 루프 방지)
                       # 실제 시간 제한 비활성화 (무한 루프 위험 있음)
                   if False:  # 항상 거짓이 되도록 변경
                       logging.warning("시뮬레이션이 10분 이상 실행되어 강제 종료합니다.")
                       sim_running = False
                       break

                   # 주기적으로 데이터 기록 (5초마다)
                   if sim_time - last_data_record >= 5:
                       time_points.append(sim_time)
                       completed_orders_points.append(sum(1 for od in orders if od.is_completed()))
                       completed_items_points.append(sum(sum(1 for item in od.items if item.picked) for od in orders))
                       last_data_record = sim_time

                   for event in pygame.event.get():
                       if event.type == pygame.QUIT:
                           logging.info("사용자가 창을 닫았습니다. 프로그램 종료합니다.")
                           pygame.quit(); sys.exit()
                       elif event.type == pygame.KEYDOWN:
                           if event.key == pygame.K_RETURN:
                               logging.info("사용자가 Enter 키를 눌러 시뮬레이션을 종료했습니다.")
                               sim_running = False
                           elif event.key == pygame.K_a:
                               simulation_speed = simulation_speed + 0.1
                               logging.info(f"시뮬레이션 속도 증가: {simulation_speed:.1f}x")
                           elif event.key == pygame.K_z:
                               simulation_speed = max(simulation_speed - 0.1, 0.1)
                               logging.info(f"시뮬레이션 속도 감소: {simulation_speed:.1f}x")
                       elif event.type == pygame.MOUSEWHEEL:
                           region_scroll_offset -= event.y * 10
                           if region_scroll_offset < 0:
                               region_scroll_offset = 0

                   screen.fill(WHITE)
                   draw_grid()
                   draw_zones()
                   draw_shelves()

                   # ── AGV 구역 표시 (얇고 밝은 테두리) ─────────────────────────
                   for i, reg in enumerate(agv_regions):
                       base_color = get_agv_color(i)
                       bright_color = (
                           min(255, base_color[0] + 100),
                           min(255, base_color[1] + 100),
                           min(255, base_color[2] + 100)
                       )
                       for x, y in reg:
                           pygame.draw.rect(
                               screen, bright_color,
                               (x*GRID_SIZE, y*GRID_SIZE, GRID_SIZE, GRID_SIZE), 1
                           )
                       for x, y in agv_label_positions[i]:
                           id_text = status_font.render(f"A-{i+1}", True, bright_color)
                           screen.blit(
                               id_text,
                               (x*GRID_SIZE + GRID_SIZE//2 - id_text.get_width()//2,
                                y*GRID_SIZE + GRID_SIZE//2 - id_text.get_height()//2)
                           )

                   # ── Human 구역 표시 ─────────────────────────────────────────
                   for j, reg in enumerate(human_regions):
                       base_color = get_agv_color(total_agvs + j)
                       bright_color = (
                           min(255, base_color[0] + 100),
                           min(255, base_color[1] + 100),
                           min(255, base_color[2] + 100)
                       )
                       for x, y in reg:
                           pygame.draw.rect(
                               screen, bright_color,
                               (x*GRID_SIZE, y*GRID_SIZE, GRID_SIZE, GRID_SIZE), 1
                           )
                       for x, y in human_label_positions[j]:
                           h_txt = status_font.render(f"H-{j+1}", True, bright_color)
                           screen.blit(
                               h_txt,
                               (x*GRID_SIZE + GRID_SIZE//2 - h_txt.get_width()//2,
                                y*GRID_SIZE + GRID_SIZE//2 - h_txt.get_height()//2)
                           )

                       # ────────────────────────────────────────────────────────────

                   # 아이템 및 AGV 그리기
                   for it in items:
                       it.draw(screen, 0, 0)
                   for a in agvs:
                       a.update(dt)
                       a.draw()

                   # Human 업데이트 및 그리기 코드 추가
                   for h in humans:
                       h.update(dt)
                       h.draw(screen, 0, 0)
                
                   # ── IDLE 상태 에이전트에게 남은 아이템 예약 기회 제공
                   for agent in agvs + humans:
                       if agent.state == "IDLE":
                          agent.find_next_item()

                   # 상태창 그리기
                   pygame.draw.rect(screen, (240,240,240), (SIM_WIDTH, 0, STATS_WIDTH, SCREEN_HEIGHT))
                   draw_stats(agvs, orders, sim_time)

                   # 정지 조건 수정: 모든 AGV와 Human이 작업을 완료하고, 움직이지 않을 때만 종료
                   all_agents = agvs + humans
                   all_delivered = all(a.state == "DELIVERED" for a in all_agents)
                   all_stationary = all(len(a.path) == 0 for a in all_agents)

                   if (all_delivered and all_stationary):
                       if all_delivered:
                           logging.info("모든 에이전트가 작업을 완료했습니다. 시뮬레이션 종료.")
                       else:
                           logging.info("더 이상 처리할 아이템이 없습니다. 시뮬레이션 종료.")
                       sim_running = False

                   pygame.display.flip()

               # Enter 키를 눌러 최종 통계를 표시하도록 대기
               waiting = True
               while waiting:
                   for event in pygame.event.get():
                       if event.type == pygame.QUIT:
                           pygame.quit(); sys.exit()
                       elif event.type == pygame.KEYDOWN and event.key == pygame.K_RETURN:
                           waiting = False

               # Enter 키를 누르면 최종 통계 화면으로 이동
               final_screen(agvs, orders, sim_time)

           except Exception as e:
               logging.error(f"시각적 시뮬레이션 중 오류: {e}")
               # 스택 트레이스 출력 (디버깅에 유용)
               import traceback
               logging.error(traceback.format_exc())
               show_error_message(f"시뮬레이션 실행 중 오류가 발생했습니다: {str(e)}")
               continue  # 메인 루프로 돌아가기

           # 종료 여부 확인 추가
           should_continue = ask_continue_or_exit()
           if not should_continue:
               logging.info("프로그램 종료합니다.")
               pygame.quit()
               sys.exit()

def ask_continue_or_exit():
   """사용자에게 계속 진행할지 종료할지 물어봅니다"""
   button_width, button_height = 300, 80
   continue_button = pygame.Rect(SCREEN_WIDTH//2 - button_width - 20, SCREEN_HEIGHT//2 - button_height//2, button_width, button_height)
   exit_button = pygame.Rect(SCREEN_WIDTH//2 + 20, SCREEN_HEIGHT//2 - button_height//2, button_width, button_height)

   screen.fill(WHITE)
   title_text = final_font.render("다음 작업을 선택하세요", True, BLACK)
   screen.blit(title_text, (SCREEN_WIDTH//2 - title_text.get_width()//2, SCREEN_HEIGHT//2 - 150))

   # 계속 버튼
   pygame.draw.rect(screen, (180, 230, 180), continue_button)
   pygame.draw.rect(screen, BLACK, continue_button, 2)
   continue_text = status_font.render("새 시뮬레이션 시작", True, BLACK)
   screen.blit(continue_text, (continue_button.centerx - continue_text.get_width()//2,
                            continue_button.centery - continue_text.get_height()//2))

   # 종료 버튼
   pygame.draw.rect(screen, (230, 180, 180), exit_button)
   pygame.draw.rect(screen, BLACK, exit_button, 2)
   exit_text = status_font.render("프로그램 종료", True, BLACK)
   screen.blit(exit_text, (exit_button.centerx - exit_text.get_width()//2,
                         exit_button.centery - exit_text.get_height()//2))

   pygame.display.flip()

   while True:
       for event in pygame.event.get():
           if event.type == pygame.QUIT:
               pygame.quit(); sys.exit()
           elif event.type == pygame.MOUSEBUTTONDOWN:
               pos = pygame.mouse.get_pos()
               if continue_button.collidepoint(pos):
                   return True  # 계속 진행
               elif exit_button.collidepoint(pos):
                   return False  # 종료
           elif event.type == pygame.KEYDOWN:
               if event.key == pygame.K_RETURN:
                   return True  # Enter 키는 계속 진행
               elif event.key == pygame.K_ESCAPE:
                   return False  # ESC 키는 종료

       clock.tick(30)

# 프로그램 시작점
if __name__ == "__main__":
   try:
       main()
   except Exception as e:
       logging.error(f"오류 발생: {e}")
       pygame.quit()
       sys.exit()
       