import random
import hashlib
from typing import List, Tuple, Dict
import os
import hashlib
import random


class GraphColoringZK:
    def __init__(self, graph_file: str = None, encoding: str = 'utf-8'):
        """Инициализация протокола с чтением графа из файла"""
        self.graph = None
        self.colors = None
        self.num_colors = 0
        self.commitments = []
        self.random_values = []
        self.permuted_colors = {}
        self.color_map = None
        self.encoding = encoding
        self.vertices_order = None
        
        if graph_file:
            self.load_graph_from_file(graph_file)
    
    def load_graph_from_file(self, filename: str):
        """Загрузка графа из файла в формате, описанном в задании"""
        with open(filename, 'r', encoding=self.encoding) as f:
            # Чтение первой строки: n и m
            n, m = map(int, f.readline().strip().split())
            
            # Инициализация графа
            self.graph = {i: [] for i in range(1, n + 1)}
            
            # Чтение ребер
            for _ in range(m):
                u, v = map(int, f.readline().strip().split())
                if u in self.graph and v in self.graph:
                    self.graph[u].append(v)
                    self.graph[v].append(u)
                else:
                    raise ValueError(f"Неверные вершины в ребре: {u} {v}")
            
            # Чтение раскраски
            self.colors = {}
            colors_line = f.readline().strip()
            if colors_line:
                colors_list = list(map(int, colors_line.split()))
                if len(colors_list) == n:
                    for i in range(1, n + 1):
                        self.colors[i] = colors_list[i - 1]
                    self.num_colors = max(self.colors.values())
                else:
                    raise ValueError("Количество цветов не соответствует количеству вершин")
    
    def create_commitment(self, vertex: int, color: int, random_value: int) -> str:
        """Создание коммитмента для вершины и ее цвета"""
        data = f"{vertex}:{color}:{random_value}"
        return hashlib.sha256(data.encode(self.encoding)).hexdigest()
    
    def verify_commitment(self, vertex: int, color: int, random_value: int, commitment: str) -> bool:
        """Проверка корректности коммитмента"""
        calculated = self.create_commitment(vertex, color, random_value)
        return calculated == commitment
    
    def prove(self) -> Tuple[List[str], List[int]]:
        """Фаза доказательства: создание коммитментов"""
        if not self.graph or not self.colors:
            raise ValueError("Граф или раскраска не установлены")
        
        commitments = []
        random_values = []
        self.permuted_colors = {}
        
        # Случайная перестановка цветов
        permutation = list(range(1, self.num_colors + 1))
        random.shuffle(permutation)
        
        # Создаем маппинг старых цветов на новые
        self.color_map = {i: permutation[i-1] for i in range(1, self.num_colors + 1)}
        
        # Создаем коммитменты для каждой вершины
        self.vertices_order = sorted(self.graph.keys())
        for vertex in self.vertices_order:
            random_value = random.getrandbits(128)
            permuted_color = self.color_map[self.colors[vertex]]
            
            # Сохраняем переставленный цвет для вершины
            self.permuted_colors[vertex] = permuted_color
            
            commitment = self.create_commitment(vertex, permuted_color, random_value)
            
            commitments.append(commitment)
            random_values.append(random_value)
        
        self.commitments = commitments
        self.random_values = random_values
        
        return commitments, random_values
    
    def get_vertex_index(self, vertex: int) -> int:
        """Получить индекс вершины в списке коммитментов"""
        if not self.vertices_order:
            self.vertices_order = sorted(self.graph.keys())
        
        try:
            return self.vertices_order.index(vertex)
        except ValueError:
            raise ValueError(f"Вершина {vertex} не найдена в списке вершин")
    
    def verify(self, challenge: Tuple[int, int]) -> Tuple[int, int, int, int, bool]:
        """Фаза верификации: ответ на вызов верификатора"""
        if not self.graph or not self.colors:
            raise ValueError("Граф или раскраска не установлены")
        
        vertex1, vertex2 = challenge
        
        # Проверяем, что вершины существуют
        if vertex1 not in self.graph or vertex2 not in self.graph:
            raise ValueError(f"Одна из вершин {vertex1} или {vertex2} не существует в графе")
        
        # Проверяем, что вершины соединены ребром
        if vertex2 not in self.graph[vertex1]:
            raise ValueError(f"Вершины {vertex1} и {vertex2} не соединены ребром")
        
        # Получаем переставленные цвета
        if vertex1 not in self.permuted_colors or vertex2 not in self.permuted_colors:
            raise ValueError(f"Цвета для вершин {vertex1} или {vertex2} не найдены")
        
        color1 = self.permuted_colors[vertex1]
        color2 = self.permuted_colors[vertex2]
        
        # Получаем индексы вершин
        idx1 = self.get_vertex_index(vertex1)
        idx2 = self.get_vertex_index(vertex2)
        
        # Получаем случайные значения
        if idx1 >= len(self.random_values) or idx2 >= len(self.random_values):
            raise ValueError("Недостаточно random значений для вершин")
        
        random1 = self.random_values[idx1]
        random2 = self.random_values[idx2]

        return color1, color2, random1, random2, color1 != color2
    
    def generate_challenge(self) -> Tuple[int, int]:
        """Генерация случайного вызова (ребра для проверки)"""
        if not self.graph:
            raise ValueError("Граф не загружен")
        
        # Выбираем случайное ребро
        edges = []
        for vertex in self.graph:
            for neighbor in self.graph[vertex]:
                if vertex < neighbor:  # Чтобы избежать дублирования
                    edges.append((vertex, neighbor))
        
        if not edges:
            raise ValueError("Граф не имеет ребер")
        
        return random.choice(edges)


class Verifier:
    """Класс верификатора для протокола ZK"""
    
    def __init__(self, graph_file: str, encoding: str = 'utf-8'):
        """Инициализация верификатора с графом"""
        self.zk = GraphColoringZK(graph_file, encoding)
        self.commitments = None
        self.vertices_order = None
        self.accepted_proofs = 0
        self.total_challenges = 0
        self.encoding = encoding
    
    def receive_commitments(self, commitments: List[str], vertices_order: List[int] = None):
        """Получение коммитментов от доказывающего"""
        self.commitments = commitments
        
        if vertices_order:
            self.vertices_order = vertices_order
        else:
            self.vertices_order = sorted(self.zk.graph.keys())
    
    def get_commitment_for_vertex(self, vertex: int) -> str:
        """Получить коммитмент для вершины"""
        if not self.commitments or not self.vertices_order:
            raise ValueError("Коммитменты или порядок вершин не установлены")
        
        try:
            idx = self.vertices_order.index(vertex)
            if idx < len(self.commitments):
                return self.commitments[idx]
            else:
                raise ValueError(f"Индекс вершины {vertex} выходит за пределы списка коммитментов")
        except ValueError:
            raise ValueError(f"Вершина {vertex} не найдена в списке вершин")
    
    def send_challenge(self) -> Tuple[int, int]:
        """Отправка вызова доказывающему"""
        return self.zk.generate_challenge()
    
    def verify_response(self, challenge: Tuple[int, int], 
                       response: Tuple[int, int, int, int, bool]) -> bool:
        """Проверка ответа от доказывающего с полной проверкой коммитментов"""
        vertex1, vertex2 = challenge
        color1, color2, random1, random2, colors_different = response
        
        print(f"\nПроверка ответа для ребра ({vertex1}, {vertex2}):")
        
        # Проверяем, что цвета разные
        if not colors_different or color1 == color2:
            print(f"    Цвета вершин одинаковы: {color1} == {color2}")
            return False
        print(f"   ✓ Цвета разные: {color1} != {color2}")
        
        # Проверяем, что вершины соединены ребром
        if vertex2 not in self.zk.graph.get(vertex1, []):
            print(f"    Вершины не соединены ребром в графе")
            return False
        print(f"   ✓ Вершины соединены ребром")
        
        # Проверяем коммитменты
        try:
            # Получаем коммитменты для вершин
            commitment1 = self.get_commitment_for_vertex(vertex1)
            commitment2 = self.get_commitment_for_vertex(vertex2)
            
            # Создаем временный объект для проверки хешей
            temp_zk = GraphColoringZK(encoding=self.encoding)
            
            # Проверяем первый коммитмент
            if not temp_zk.verify_commitment(vertex1, color1, random1, commitment1):
                print(f"   ❌ Неверный коммитмент для вершины {vertex1}")
                print(f"      Ожидалось: {commitment1}")
                print(f"      Получено: {temp_zk.create_commitment(vertex1, color1, random1)}")
                return False
            print(f"   ✓ Коммитмент для вершины {vertex1} проверен")
            
            # Проверяем второй коммитмент
            if not temp_zk.verify_commitment(vertex2, color2, random2, commitment2):
                print(f"   ❌ Неверный коммитмент для вершины {vertex2}")
                print(f"      Ожидалось: {commitment2}")
                print(f"      Получено: {temp_zk.create_commitment(vertex2, color2, random2)}")
                return False
            print(f"   ✓ Коммитмент для вершины {vertex2} проверен")
            
        except ValueError as e:
            print(f"   Ошибка при проверке коммитментов: {e}")
            return False
        except Exception as e:
            print(f"   Неожиданная ошибка: {e}")
            return False
        
        self.total_challenges += 1
        self.accepted_proofs += 1
        
        print(f"   Все проверки пройдены успешно!")
        return True
    
    def run_verification(self, prover: 'Prover', rounds: int = 20) -> bool:
        """Запуск нескольких раундов верификации"""
        for round_num in range(1, rounds + 1):
            print(f"\n{'='*40}")
            print(f"Раунд {round_num}/{rounds}")
            print('='*40)
            
            print("1. Прувер создает коммитменты...")
            commitments, random_values = prover.prove()
            
            # Передаем коммитменты и порядок вершин верификатору
            vertices_order = prover.zk.vertices_order
            self.receive_commitments(commitments, vertices_order)
            print(f"   Получено {len(commitments)} коммитментов")
            
            print("2. Верификатор выбирает ребро для проверки...")
            challenge = self.send_challenge()
            print(f"   Выбрано ребро: {challenge}")
            
            print("3. Прувер готовит ответ...")
            response = prover.respond_to_challenge(challenge)
            
            print("4. Верификатор проверяет ответ...")
            if not self.verify_response(challenge, response):
                print(f"\nРаунд {round_num} ПРОВАЛЕН")
                return False
            
            print(f"\n✅ Раунд {round_num} ПРОЙДЕН")
        
        success_rate = self.accepted_proofs / self.total_challenges if self.total_challenges > 0 else 0
        print(f"\n{'='*50}")
        print(f"📊 Статистика проверки:")
        print(f"   Успешных раундов: {self.accepted_proofs}/{self.total_challenges}")
        print(f"   Процент успеха: {success_rate*100:.1f}%")
        print('='*50)
        
        return success_rate > 0.95


class Prover:
    """Класс доказывающего для протокола ZK"""
    
    def __init__(self, graph_file: str, coloring: Dict[int, int] = None, encoding: str = 'utf-8'):
        """Инициализация доказывающего с графом и раскраской"""
        self.zk = GraphColoringZK(graph_file, encoding)
        print(f"   Раскраска прувера: {self.zk.colors}")
    
    def prove(self) -> Tuple[List[str], List[int]]:
        """Создание доказательства"""
        return self.zk.prove()
    
    def respond_to_challenge(self, challenge: Tuple[int, int]) -> Tuple[int, int, int, int, bool]:
        """Ответ на вызов верификатора"""
        return self.zk.verify(challenge)


def create_example_graph_file(filename: str = "graph.txt", encoding: str = 'utf-8'):
    """Создание примера файла с графом"""
    example_graph = """4 5
1 2
1 3
1 4
2 3
3 4
1 2 3 2
"""
    
    with open(filename, 'w', encoding=encoding) as f:
        f.write(example_graph)
    
    print(f"Создан файл графа: {filename}")
    return filename

def main():
    """Основная функция демонстрации работы протокола"""
    print("=== Доказательство с нулевым разглашением для задачи раскраски графа ===")
    graph_file = create_example_graph_file()
    
    print("\nИнициализация участников протокола...")
    prover = Prover(graph_file)
    verifier = Verifier(graph_file)
    
    print(f"   Граф загружен: {len(prover.zk.graph)} вершин")
    print(f"   Используется {prover.zk.num_colors} цветов для раскраски")
    
    rounds = 20
    print("\nЗапуск протокола с нулевым разглашением...")
    print(f"   Выполняется {rounds} раундов доказательства...")
    
    success = verifier.run_verification(prover, rounds)
    
    if success:
        print("\n✓ Доказательство ПРИНЯТО: доказывающий знает правильную раскраску графа")
        print(f"  Успешных раундов: {verifier.accepted_proofs}/{verifier.total_challenges}")
    else:
        print("\n✗ Доказательство ОТКЛОНЕНО")
        print(f"  Успешных раундов: {verifier.accepted_proofs}/{verifier.total_challenges}")

    # Очистка
    if os.path.exists(graph_file):
        os.remove(graph_file)
    
    print("\n=== Демонстрация завершена ===")

if __name__ == "__main__":
    main()